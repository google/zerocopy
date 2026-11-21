# Floating-point control state as interface state: procedure, thread, signal, loader, plug-in and task boundaries

## Summary

Rounding direction, flush-to-zero (FTZ), denormals-are-zero (DAZ), exception masks and sticky exception flags are ambient machine state. They change what a callee computes, yet no mainstream interface type carries them. Each kind of component boundary has its own contract, and the contracts disagree:

- **Procedure call.** Fortran, the System V x86-64 psABI and the Microsoft x64 convention all make control modes callee-preserved. They differ on flags and on who pays:
  - Fortran requires the processor to restore rounding, underflow and halting modes on return. It hides the caller's signaling flags from the callee and merges the callee's new flags back.
  - The psABI makes the MXCSR control bits and the x87 control word callee-saved and the status bits caller-saved.
  - Microsoft adds a caller-side duty: a caller that changed the nonvolatile fields must restore the standard values before calling, unless there is an agreement. Microsoft also says no unwind descriptor records the saved MXCSR.
  - AAPCS64 treats FPCR as global state that only specific support functions may change, and FPSR as not preserved.
  - C11 states the same model only as "programming conventions".
- **Thread creation.** C11 7.6p2, POSIX `pthread_create` and the psABI all specify inheritance from the creating thread. On Linux x86-64 the kernel's `fpu_clone` copies the parent's FPU registers. In a probe, the child thread also inherited a sticky flag (PE). No Microsoft statement on new threads was found.
- **Signal delivery.** C11 leaves the floating-point environment unspecified in a handler. POSIX says nothing. Linux x86 resets the user FPU state to its init value before the handler runs (MXCSR `0x1F80`, x87 control word `0x037F`) and restores the interrupted state from the signal frame on `sigreturn`. A probe confirmed both, and showed that a handler's own change does not leak.
- **Dynamic loading.** GCC's `crtfastmath.o` constructor ORs FTZ+DAZ (`0x8040`) into MXCSR. Since GCC 13 it is no longer linked for `-shared` on x86 GNU/Linux unless `-mdaz-ftz` is given. In probes with GCC 15.2 and Clang 19.1.7, a `-ffast-math -shared` library left MXCSR unchanged when loaded, while a `-mdaz-ftz` library changed it to `0x9FC0`. A 2022 survey of Python wheels found 5,830 affected shared libraries among about 2.4 million scanned, in 49 packages.
- **Compiler IR.** LLVM records a function's assumed denormal mode in `denormal_fpenv`; the default is `ieee|ieee`. LLVM explicitly does not enforce the mode. The inliner refuses to inline across incompatible modes unless the callee's mismatched component is `dynamic`. The linker reported no mismatch.
- **Plug-in hosting.** JUCE's `ScopedNoDenormals` sets DAZ+FTZ on construction and restores the saved MXCSR on destruction. Because it restores the whole register, sticky flags raised inside the scope are discarded on x86. JUCE's plug-in templates place it at the top of `processBlock`.
- **Task scheduling.** At the pinned Julia revision, the control bits are task-local: they are saved at switch-out, inherited at task creation and restored at switch-in on any thread. The runtime runs inference, codegen and finalizers under the default state. Sticky flags are not preserved across switches.

Cost matters because subnormal operands are slow. On the probe host (Ice Lake server, KVM guest), a dependent chain of scalar double multiplies took about 35–40 ns per operation with subnormal operands, against about 1.2 ns for normal ones (about 30×). With FTZ+DAZ set there was no difference. A direct `stmxcsr`/`ldmxcsr` save-and-restore pair cost 4.8 ns. Glibc `fegetenv`/`fesetenv` cost 133–144 ns, and a gfortran procedure that uses the IEEE modules cost 231–244 ns per call, against 2.7–2.8 ns without them.

## Applicability

**Subjects and their relationship.** This is a comparison across boundary kinds. Each subject is the authority for one boundary or one implementation of it:

| Boundary | Normative or defining subject | Implementation examined |
|---|---|---|
| Procedure call | Fortran 2023 draft J3/23-007r1, clause 17 and 18.10.3; C11 draft N1570 7.6; System V psABI 1.0; Microsoft x64 calling convention; AAPCS64 2026Q3 | gfortran (GCC source and GCC 15.2 execution) |
| Thread creation | C11 7.6p2; POSIX `pthread_create`; psABI "Thread State" | Linux `fpu_clone`; glibc 2.43 execution |
| Signal delivery | C11 5.1.2.3p5; POSIX (silent) | Linux x86 `handle_signal`, `fpu__clear_user_states`, `fpu__restore_sig`; execution |
| Dynamic loading | none (toolchain behaviour) | GCC `crtfastmath.c` and the x86 spec; GCC 15.2 and Clang 19.1.7 execution; Python wheel survey |
| Compiler IR | LLVM LangRef `denormal_fpenv` | LLVM `Attributes.td`, `Attributes.cpp`; LLVM 19.1.7 and 21.1.8 execution |
| Plug-in callback | none (framework convention) | JUCE `ScopedNoDenormals` (source only) |
| Task switch | Julia `set_zero_subnormals` documentation | Julia runtime `task.c`, `julia_internal.h` (source only) |

**Revisions.**
- Source findings hold at the pinned revisions in `REPORT.json`. Some are recent:
  - LLVM's first-class `denormal_fpenv` replaced the string attributes `"denormal-fp-math"` and `"denormal-fp-math-f32"` in commit `2502e3b7badc` (2026-02-05). The released LLVM 19 and 21 used in the probes still use the string attributes.
  - Julia's task-local control state arrived in commit `b72cfb3c9e63` (2026-11-17), which is newer than any Julia release examined. Before it, the docstring said "This function only affects the current thread."
- The probes ran on released toolchains (GCC/GNU Fortran 15.2.0, Clang 19.1.7, LLVM 19.1.7 and 21.1.8, glibc 2.43, Linux 7.1.6) on one x86-64 KVM guest: Intel Xeon, CPU family 6 model 106 (Ice Lake server), 2.60 GHz nominal.
- I claim that the inliner rule at the pinned LLVM revision matches the released versions' behaviour only by comparing source with the execution of older releases (derived).

**Out of scope.** Decimal floating point, GPU denormal modes (LLVM's `float:` override is documented as honoured by AMDGPU and NVPTX only), the x87 precision-control interaction with `long double`, and language-level APIs other than Fortran's IEEE modules, C `<fenv.h>`, and Julia's.

## Findings

### 1. Vocabulary and the MXCSR layout

On x86-64, SSE arithmetic is governed by MXCSR:

- bits 0–5 are the sticky status flags IE, DE, ZE, OE, UE and PE;
- bit 6 is DAZ;
- bits 7–12 are the exception masks;
- bits 13–14 are the rounding control RC;
- bit 15 is FTZ.

The power-on and process-start value is `0x1F80` (all exceptions masked, round to nearest, no FTZ or DAZ). The x87 unit has a separate control word: `0x037F` at Linux process start (extended precision) and double precision under the Microsoft convention. Linux's init state sets `cwd = 0x37f` and `mxcsr = MXCSR_DEFAULT`, where `MXCSR_DEFAULT` is `0x1f80` (`arch/x86/kernel/fpu/core.c:558-562`, `arch/x86/include/asm/fpu/types.h:72`). AArch64 splits the same state across two registers: FPCR holds the control bits (RMode bits 22–23, FZ bit 24, trap enables bits 8–12, AH/FIZ bits 0–1) and FPSR holds the cumulative flags.

The rest of this report separates **control modes** (rounding, FTZ/DAZ, masks, precision) from **status flags** (sticky exceptions), because every contract below treats them differently.

### 2. Procedure-call contracts

| Contract | Control modes across a call | Status flags across a call | Who restores | Unwinding |
|---|---|---|---|---|
| Fortran 2023 draft, 17.3–17.6 | "the processor shall not change the rounding modes on entry, and on return shall ensure that the rounding modes are the same as they were on entry". The same rule applies to underflow and halting modes, except in `IEEE_SET_*`/`IEEE_SET_STATUS` | Signaling on entry: set quiet on entry, restored to signaling on return. New signals are not cleared on return | the processor (compiler and runtime) | not addressed |
| Fortran 18.10.3 (non-Fortran procedures) | "shall not alter the floating-point status (17.7) other than by setting an exception flag to signaling" | flags on entry are processor dependent | the foreign procedure (an obligation, not checked) | not addressed |
| C11 N1570 7.6p3 | a call "does not alter its caller's floating-point control modes ... unless the function is so documented"; callees assume default modes | callees may raise exceptions; they do not clear or depend on the caller's flags | convention only | not addressed |
| System V psABI 1.0 | "The control bits of the MXCSR register are callee-saved ... The x87 status word register is caller-saved, whereas the x87 control word is callee-saved." | MXCSR status bits caller-saved | callee | not addressed |
| Microsoft x64 | MXCSR[6:15] and the x87 FPCSR are nonvolatile. Callee restores; "a caller that has modified any of these fields must restore them to their standard values before invoking a callee, unless by agreement the callee expects the modified values" | MXCSR[0:5] volatile; "Make no assumptions" | callee **and** caller | "there is no static unwind descriptor"; use a C++ destructor or `__finally` |
| AAPCS64 2026Q3 | FPCR is "a global register". Its control bits "may be modified by calls to specific support functions that affect the global state of the application"; NEP must be zero at public interfaces | FPSR "not preserved across a public interface" | the support functions | not addressed |

Basis: normative (Fortran draft; C11 draft; psABI; AAPCS64) + documentation (Microsoft).

**Two exceptions in Microsoft's rules.** The convention allows violations "in functions where the documented purpose of the given function is to modify the nonvolatile ... flags", and "when it's provably correct that the violation ... results in a program that behaves the same ... for example, through whole-program analysis". Its `setjmp` saves MXCSR and its `longjmp` restores it (`x64-calling-convention.md:183-189, 206-214, 220`). Basis: documentation.

**Fortran's scope rule and its implementation.** The rules in 17.3–17.6 say "a procedure", not "a procedure that accesses the IEEE modules". For scoping units that do not access the modules, 17.1 para 3 makes support processor dependent and only requires that a flag signaling on entry still signals on exit. Note 3 of 17.7 says "The processor is required to ensure that a call to a Fortran procedure does not change the floating-point status other than by setting exception flags to signaling."

gfortran implements save and restore **only** in procedures whose namespace references a symbol from `IEEE_FEATURES`, `IEEE_EXCEPTIONS` or `IEEE_ARITHMETIC`:

- `is_ieee_module_used` decides this (`gcc/fortran/trans-decl.cc:7334-7339`).
- If it holds, the compiler emits `gfc_save_fp_state` into the procedure's init block and `gfc_restore_fp_state` into its cleanup (`:8466-8470`, `:8610-8612`).
- At run time these call `_gfortran_ieee_procedure_entry` and `_gfortran_ieee_procedure_exit` (`libgfortran/ieee/ieee_helper.c:167-203`):
  - Entry saves the state and clears all flags.
  - Exit reads the current flags, restores the entry state, then re-raises the flags read.
- The libgfortran source comment cites "Fortran 2008's 14.3 paragraph 3, note 14.4, 14.4 paragraph 4, 14.5 paragraph 2, and 14.6 paragraph 1".
- On x86 the state is saved with `fnstenv` plus `stmxcsr` and restored with `fldenv` plus `ldmxcsr` (`libgfortran/config/fpu-387.h:430-455`).

Basis: normative + source.

**Execution (gfortran 15.2, `probes/fortran_modes.f90`).**
- A procedure that uses `IEEE_ARITHMETIC` and calls `IEEE_SET_ROUNDING_MODE(IEEE_DOWN)` returns with the caller still at nearest.
- A Fortran procedure that does *not* use the IEEE modules and calls a C function doing `fesetround(FE_DOWNWARD)` leaks the mode to its caller: `fegetround()` returns `1024`.
- The same C call made from a procedure that does use the modules is undone at that procedure's exit: `fegetround()` returns `0`.
- A callee sees `IEEE_OVERFLOW` quiet on entry even when the caller's flag is signaling. The caller's flag is signaling again after return, and an overflow inside the callee propagates to the caller.

Basis: execution. The leak is consistent with 18.10.3, which puts the obligation on the C procedure. It shows that the protection is not a property of every Fortran call boundary in this implementation.

### 3. Thread creation

The three defining texts agree that a new thread inherits the floating-point environment:

- **C11 N1570 7.6p2:** "The floating-point environment has thread storage duration. The initial state for a thread's floating-point environment is the current state of the floating-point environment of the thread that creates it at the time of creation."
- **POSIX `pthread_create`:** "The floating-point environment shall be inherited from the creating thread." The Issue 6 change history records that this was made explicit.
- **psABI "Thread State":** "New threads inherit the floating-point state of the parent thread and the state is private to the thread thereafter."

Basis: normative.

**Linux implementation.** `fpu_clone` (`arch/x86/kernel/fpu/core.c:677-740`) handles two cases:
- For kernel threads and I/O workers (`minimal`), it copies `init_fpstate`, under the comment "No FPU state inheritance for kernel threads and IO worker threads" (`:703-710`).
- For user tasks, it reloads the parent's registers if needed and then calls `save_fpregs_to_fpstate(dst_fpu)` (`:729-731`). This copies the parent's live MXCSR and x87 state, flags included.

Basis: source.

**Execution (glibc 2.43, Linux 7.1.6, `probes/fpenv_boundaries.c`).** The parent set MXCSR to `0xBFE0`: FTZ, DAZ, RC=down, and the PE flag. It set the x87 control word to `0x067F`. A `pthread_create` child read exactly `0xBFE0` and `0x067F`. Inheritance therefore covers sticky status flags, not only control bits. C11's "floating-point environment" includes flags (7.6p1), so this is conforming. Basis: execution.

**Windows.** No Microsoft documentation stating whether a new thread inherits or resets MXCSR or the x87 control word was found (CreateThread, `_beginthreadex`, `_controlfp`, `/fp`, CRT floating-point support and `_fpreset` pages were searched). A mingw-w64 patch email dated 2026-10-18 states that winpthreads previously called `_fpreset()` in new threads. According to the email, that reset the x87 word to `0x037F` and left MXCSR at the Windows default; the author's own wording is "discarding whatever the creating thread had set". This is a third-party claim about one runtime library, not a Windows specification. Basis: documentation (secondary).

### 4. Signal delivery

**C11 5.1.2.3p5.** When the abstract machine is interrupted by a signal, the values of most objects "are unspecified, as is the state of the floating-point environment". The environment "becomes indeterminate when the handler exits ... if it is modified by the handler and not restored to its original state." POSIX's `sigaction` and Signal Concepts pages say nothing about the floating-point environment, and no `<fenv.h>` function is on POSIX's async-signal-safe list. Basis: normative.

**Linux x86 implementation.**
- `handle_signal` in `arch/x86/kernel/signal.c:307-310` does the following after building the frame: "Ensure the signal handler starts with the new fpu state." `fpu__clear_user_states(fpu);`
- That function (`fpu/core.c:849-874`) calls `restore_fpregs_from_init_fpstate(XFEATURE_MASK_USER_RESTORE)`.
- The interrupted state was saved to the user signal frame by `copy_fpstate_to_sigframe` (`fpu/signal.c:205`). `fpu__restore_sig` (`fpu/signal.c:462`) reloads it on `sigreturn`.
- On x86-64, a frame whose MXCSR has bits outside `mxcsr_feature_mask` is rejected (`fpu/signal.c:409-411`).

Basis: source.

**Execution.**
- Inside a `SIGUSR1` handler raised while MXCSR was `0xBFE0` and the x87 word `0x067F`, the handler read `0x1F80` and `0x037F`.
- The handler then set round-toward-zero. After `sigreturn` the interrupted code again read `0xBFE0` and `0x067F`.
- So handlers get a fresh default state, and their changes do not leak. That includes sticky flags they raise, which are lost.
- The only way for a handler to change the interrupted context's mode is to edit the saved frame. That path was not exercised.

Basis: execution.

### 5. Dynamic loading and process start

**Mechanism.** In `libgcc/config/i386/crtfastmath.c:82-98`, a `__attribute__((constructor))` named `set_fast_math` runs, on x86-64, `mxcsr |= MXCSR_DAZ | MXCSR_FTZ` (bits 6 and 15) with `stmxcsr` and `ldmxcsr`. The x86 GNU/Linux driver spec is in `gcc/config/i386/gnu-user-common.h:49-53`:

```text
%{mdaz-ftz:crtfastmath.o%s;Ofast|ffast-math|funsafe-math-optimizations:%{!shared:%{!mno-daz-ftz:crtfastmath.o%s}}}
```

The spec gained `!shared` and `-mdaz-ftz` in commit `e54375d85d4a` (authored 2022-12-12, "x86: Add a new option -mdaz-ftz ..."). GCC bug 55522, reported 2012-11-29, is RESOLVED FIXED with target milestone 13.0. Its comment 45 reads "Fixed for GCC 13", and the other ports were changed in January 2023. The GCC 13 release notes say that these options "will no longer add startup code to alter the floating-point environment when producing a shared object with -shared". Basis: source + documentation.

**Execution (`probes/run_all.sh` sections 1–2).**

| Artifact | MXCSR effect |
|---|---|
| `gcc -O2 -ffast-math` executable | `0x9FC0` at `main` |
| `gcc -O2 -ffast-math -mno-daz-ftz` executable | `0x1F80` |
| `clang-19 -O2 -ffast-math` executable | `0x9FC0` (the driver links `crtfastmath.o`) |
| `gfortran -O2 -ffast-math` executable | `IEEE_GET_UNDERFLOW_MODE` reports abrupt underflow |
| `dlopen` of `gcc -ffast-math -shared` library | `0x1F80` → `0x1F80` |
| `dlopen` of `gcc -ffast-math -mdaz-ftz -shared` library | `0x1F80` → `0x9FC0` |
| `dlopen` of `clang-19 -ffast-math -shared` library | `0x1F80` → `0x1F80` |

Basis: execution. Loader-time behaviour of GCC releases before 13 was not executed here.

**Per-thread effect.** The constructor writes the MXCSR of whichever thread runs it. In GCC bug 55522 comment 19, Dolan-Gavitt noted that "FTZ/DAZ will only be set in the CPU state of the thread that loaded the shared library". Combined with §3, threads created *after* the load inherit the change, while existing threads do not. That part is derived and was not executed here. Basis: documentation + derived.

**Field survey (Dolan-Gavitt, 2022-09-06).**
- Method: fetched metadata for 386,544 PyPI packages; downloaded 269,752 manylinux x86-64 wheels, about 4 TB; statically matched the `stmxcsr`/`or 0x8040`/`ldmxcsr` constructor in `.init_array`.
- Shared libraries: 5,830 affected out of about 2.4 million scanned.
- Packages: "only 49 packages ... at some point in their history" shipped one. The largest counts of affected files were BTrees (1,166), gevent (1,054) and qiskit-aer (589).
- Reach: through deps.dev reverse dependencies, "A total of 2,514 packages eventually depend on a package that uses -ffast-math", with "at least 9.7 million downloads over the past 30 days". The author marks the dependency count as approximate.
- The author also reports that under `-Ofast`, `-fno-fast-math` does not disable fast math.

Basis: documentation (secondary measurement).

### 6. Compiler IR: LLVM `denormal_fpenv`

**Semantics** (`llvm/docs/LangRef.md:2888-2938`).
- `denormal_fpenv` "indicates the denormal (subnormal) handling that may be assumed for the default floating-point environment". Its base form is a `|`-separated output|input pair over `ieee`, `preservesign`, `positivezero` and `dynamic`.
- It has an optional `float:` override for 32-bit floats, respected by AMDGPU and NVPTX only.
- If it is absent, "the default is `ieee|ieee`". `dynamic` means the behaviour "is derived from the dynamic state of the floating-point environment", and transformations that depend on denormal behaviour "should not be performed".
- The key disclaimer reads: "this does not make any attempt to ensure the mode is consistent. User or platform code is expected to set the floating point mode appropriately before function entry."
- The general model (`LangRef.md:4352-4362`) assumes round-to-nearest and preserved subnormals. Running outside those assumptions "typically leads to undefined behavior" unless `strictfp`, `denormal_fpenv` or constrained intrinsics weaken them.

Basis: normative (LLVM IR reference).

**Merging rules** (`llvm/include/llvm/IR/Attributes.td`).
- `def DenormalFPEnv : IntAttr<"denormal_fpenv", IntersectPreserve, [FnAttr]>;` (`:431`). `IntersectPreserve` means that when two call sites' attributes are intersected, "both must be present and equal" (`:33-36`).
- Inlining uses `def : CompatRule<"checkDenormMode">;` (`:487`) next to `checkStrictFP` (`:488`). There is no `MergeRule` for the attribute: a caller's attribute is never adjusted to absorb a callee's.

**Inline compatibility** (`llvm/lib/IR/Attributes.cpp:2614-2653`). `denormModeCompatible(Caller, Callee)` holds if the two modes are equal, or the callee is fully `dynamic`. Otherwise it holds only if one component matches and the callee's other component is `dynamic`. `checkDenormMode` applies this rule to the default modes and then to the effective f32 modes. `checkStrictFP` forbids inlining a `strictfp` callee into a non-`strictfp` caller.

Basis: source.

**Execution with released LLVM (string-attribute era; `probes/llvm/`).**
- `clang-19 -fdenormal-fp-math=preserve-sign` emits `"denormal-fp-math"="preserve-sign,preserve-sign"`. `=dynamic` emits `"dynamic,dynamic"`.
- After `llvm-link` of a default (ieee) caller with each callee and `opt -passes='cgscc(inline)'`, both LLVM 19.1.7 and 21.1.8 left the call to a `preserve-sign` callee in place. They inlined the `dynamic` and `ieee` callees.
- `llvm-link` printed no diagnostic for the mismatch in any case.

Basis: execution.

**Observation, not a claim of defect.**
- `clang-19 -O2 -ffast-math` emitted **no** `denormal-fp-math` attribute, so the IR is at the documented default `ieee|ieee`.
- The same driver links `crtfastmath.o` into executables, which then run with FTZ+DAZ (§5).
- So in this release the IR's documented assumption and the run-time mode differ for `-ffast-math` executables.
- Whether this is intended (fast-math flags already license value changes) was not examined. No upstream defect is claimed.

Basis: execution + derived.

**Implication for linking components built with different flags** (derived from the above). Nothing in the IR or at link time reconciles the modes. Each function carries an *assumption*. The only enforcement is the inliner's refusal, which prevents an optimizer from silently importing one function's assumption into another. Nothing sets the hardware mode at a call boundary. A call from an `ieee` function to a `preservesign` function across a module boundary is therefore a contract with no runtime check.

### 7. Plug-in hosting: JUCE

`juce::ScopedNoDenormals` (`modules/juce_audio_basics/buffers/juce_FloatVectorOperations.h:225-241`, `.cpp:1544-1562`) works as follows:

- The constructor reads the status register through `getFpStatusRegister()`, ORs in `0x8040` (DAZ+FTZ) on SSE, and writes it back. On AArch64 it ORs FZ (bit 24) into FPCR; on 32-bit NEON it uses FPSCR.
- The destructor writes back the saved value.
- On Windows-on-Arm under MSVC, `_control87(0, 0) & _MCW_DN` is used instead (`.cpp:1438-1493`).
- `disableDenormalisedNumberSupport` and `enableFlushToZeroMode` are the non-scoped forms (`.h:202-214`).

The Projucer audio-plugin template (`extras/Projucer/Source/BinaryData/Templates/jucer_AudioPluginFilterTemplate.cpp:133`) and the CMake example (`examples/CMake/AudioPlugin/PluginProcessor.cpp:129`) put `juce::ScopedNoDenormals noDenormals;` first in `processBlock`. GitHub code search found no use of `ScopedNoDenormals` in the plug-in client wrappers themselves. So the guard is placed by the plug-in author, on the plug-in's side of the host callback. Basis: source.

**Flag erasure (derived from source).** On x86 the saved value is the entire MXCSR, including sticky flags (bits 0–5). Any exception flag raised inside the guarded scope is cleared when the destructor runs. This is permitted by the Microsoft and psABI conventions, which do not preserve status flags, but it differs from Fortran's merge-on-return rule. On AArch64 the saved register is FPCR, which holds no flags, so flags in FPSR survive. JUCE was not built and executed for this report.

### 8. Task scheduling: Julia

At the pinned revision, `julia_internal.h:1583-1611` defines `jl_fpctrl_get`. On x86 it executes `stmxcsr` and `fnstcw` and masks off MXCSR bits 0–5. `jl_fpctrl_set` executes `ldmxcsr` and `fldcw`, and `JL_FPCTRL_DEFAULT` is `(0x37f << 32) | 0x1f80`.

In `src/task.c`, the state flows as follows:
- `lastt->fpctrl = jl_fpctrl_get();` runs at switch-out (`:518`).
- `jl_fpctrl_restore(ct->fpctrl);` runs at switch-in (`:717`) and at task start (`:1262`).
- A new task inherits its parent's state (`:1142-1143`, comment "a new task inherits the floating-point control state of its parent").
- The task struct gains a `uint64_t fpctrl` field (`julia_threads.h:566`).

On x86 the restore is unconditional. On AArch64 it is guarded by a comparison, because the costs of reading and writing are inverted (`julia_internal.h:1712-1726`). `jl_fpctrl_enter_default` (`:1735-1740`) wraps type inference, codegen and finalizers so that they run under the default state; `src/gf.c:474-614` has three such sites. The `set_zero_subnormals` docstring (`base/rounding.jl:308-313`) states the contract: "local to the current task ... a new task inherits the setting of the task that created it, and the setting is restored whenever the task resumes running, on whichever thread that happens."

The commit's NEWS entry states that "The sticky exception status flags are not preserved across task switches, nor across any of those runtime entries". The masked `jl_fpctrl_get` combined with the unconditional x86 `ldmxcsr` implies that flags are cleared at every switch-in (derived).

Basis: source + documentation. Julia was not executed for this report.

### 9. Cost and resource footprint (L1–L6)

| Level | Quantity | Value | Basis |
|---|---|---|---|
| L4 | Scalar double multiply, dependent chain, normal vs subnormal operand, FTZ/DAZ off | 1.18–1.22 vs 35.3–39.7 ns/op (about 30×) | measured, `denormal_cost.c`, six runs over three invocations |
| L4 | Same, 8 independent chains | 0.148–0.154 vs 4.35–4.97 ns/op | measured |
| L4 | Same with FTZ+DAZ on | normal and subnormal both 1.18–1.21 ns/op (chain; one earlier run showed a single 1.58 ns/op outlier) and 0.148–0.154 ns/op (independent) | measured |
| L4 | Cycles per subnormal chain step at the 2.60 GHz nominal clock | about 92–103 cycles (35.3–39.7 ns × 2.6) | derived; the actual core clock under KVM was not measured |
| L4 | Core i7 with SSE, normal vs subnormal-input multiply | 4 vs "over 200" cycles | cited (Andrysco et al. 2015, §II.C) |
| L4 | `stmxcsr`+`ldmxcsr` save/restore pair | 4.74–4.79 ns | measured, `save_restore_cost.c` |
| L4 | MXCSR plus x87 CW pair | 4.75–5.23 ns | measured |
| L4 | glibc `fegetenv`+`fesetenv` pair | 133–144 ns | measured |
| L4 | glibc `fegetround`+`fesetround` pair | 11.4–12.0 ns | measured |
| L4 | gfortran call to an IEEE-module-using procedure vs a plain procedure | 231–244 vs 2.7–2.8 ns/call | measured, `fortran_call_cost.f90` |
| L4 | Julia `yieldto` round trip, before vs after task-local control state; `fegetenv` variant | 121 → 127 ns; 319 ns | cited (Julia commit `b72cfb3c9e63` message, AMD EPYC 9354) |
| L4 | x87 `fnstenv`/`fldenv` | "about 60 ns each on Zen 4" | cited (same commit message) |
| L6 | `crtfastmath.o` (GCC 15.2) | 108 bytes text, 8 bytes data | measured (`size`) |
| L6 | Per-task state in Julia | 8 bytes (`uint64_t fpctrl`) | source |
| L6 | gfortran per-procedure state buffer | `GFC_FPE_STATE_BUFFER_SIZE` (value not examined) | source |
| L1 | Authoring or repair effort for mode-safe code | not measured | — |
| L2 | Toolchain build time or memory | not measured | — |
| L3 | Compile-time cost of the inliner check or attribute parsing | not measured | — |
| L5 | Certificate or proof checking | not applicable; no subject produces certificates | — |

The Julia commit message also cites per-core `stmxcsr`/`ldmxcsr` latencies from uops.info: about 14–16 cycles to read on AMD Zen, against 1 cycle on Intel Sandy Bridge through Emerald Rapids. That table is second-hand and was not verified here.

### 10. Comprehensibility (C1) and model refinement (C2)

**C1, what a reader must hold in mind.** To know which mode a statement runs under, a reader must track:
1. the process-start value (toolchain and link flags, §5);
2. any constructors of loaded libraries and which thread ran them;
3. the creating thread's state at each `pthread_create` (§3);
4. whether the code is in a signal handler (§4);
5. the callee-restore discipline of every procedure on the stack (§2), including non-Fortran callees that Fortran does not police;
6. in Julia, the task identity rather than the thread (§8).

None of these is visible in a function signature. The most legible contracts are Fortran's, which are local (each procedure restores) and enforced by the processor for module-using procedures, and Julia's, which is one rule stated in one docstring. The least legible is shared-library loading, because the effect is non-local in both space (the whole process) and time (later threads). Diagnostics are absent everywhere: no linker, loader or runtime reports a mode mismatch (§5, §6).

**C2, one model covering every case.** Each mechanism above is an instance of a dynamically scoped parameter with two orthogonal channels:

- **Control channel, a value.** Every boundary picks one of three policies:
  - *inherit*: thread creation, task creation, procedure entry under every call ABI;
  - *reset to default*: signal-handler entry, Julia runtime entry, and the Microsoft caller duty before calling;
  - *restore on exit*: Fortran, the psABI and Microsoft callee duty, JUCE's destructor, Julia switch-in, `sigreturn`.
  Loader constructors are the one mechanism that *mutates* the parameter without a scope.
- **Flag channel, a monoid (bitwise OR).** Every boundary picks one of three policies:
  - *merge*: Fortran return; Linux thread creation by inheritance;
  - *discard*: Linux signal return; JUCE on x86; Julia task switch;
  - *unspecified*: C, the psABI, Microsoft.

With this vocabulary, the special cases are ordinary choices. The Microsoft double obligation is reset-before-call plus restore-on-exit. The JUCE flag loss is restore-on-exit applied to a register that packs both channels. The gfortran leak is restore-on-exit applied only to some procedures. A toolchain that made the two channels explicit in its interface would make each boundary's choice auditable: a `with_fp_mode(m, f)` scope plus an explicit flag-accumulation result.

That model does not remove three costs:
- unwinding must still restore the parameter, and Microsoft documents that no unwind descriptor does it;
- asynchronous entry (signals) needs a reset policy that the language cannot enforce;
- an optimizer needs a static approximation of the parameter to constant-fold. That is what `denormal_fpenv` supplies, and `dynamic` is its escape hatch.

So the hidden complexity moves into the compiler's static mode annotation rather than disappearing.

### 11. Validation (V1–V4)

- **V1 (specification adequacy).** None of the subjects publishes conformance tests for the procedure-boundary or thread-boundary rules that were found here. The probes in `support/probes/` act as minimal conformance tests for the Linux, glibc, GCC and LLVM rows. The Julia commit adds 44 lines to `test/rounding.jl` (source diff statistics; its contents were not examined).
- **V2 (lowering soundness).** The LLVM inliner rule is a static guard. No differential or metamorphic testing of denormal-mode handling across compilers was found or run. The `-ffast-math` attribute observation in §6 is the kind of mismatch such testing would target.
- **V3 (concurrency and asynchrony).** The signal and thread probes are single-run observations, not systematic tests. Races, such as a library loaded while other threads compute, were not exercised.
- **V4 (field evidence).**
  - The Python wheel survey is field evidence for the loading boundary.
  - Di Franco, Guo and Rubio-González (ASE 2017) studied 269 numerical bugs from NumPy, SciPy, LAPACK, the GNU Scientific Library and Elemental: accuracy 14%, special values 28%, convergence 21%, correctness 37%. These figures come from the abstract and the authors' slides. Their slides list "Compiler optimizations violating semantics of mathematical operations" as a common correctness bug, but no category for floating-point environment or control state was found in the material read.
  - No incident study for the signal, thread or plug-in boundaries was found.

## Boundaries

- **Windows thread creation:** unknown. No Microsoft documentation was found, and nothing was executed on Windows. The mingw-w64 claim is secondary and concerns one runtime library.
- **Windows exceptions, APCs and fibers:** not examined.
- **macOS, AArch64 Linux and RISC-V:** not examined by execution. AArch64 statements come from AAPCS64, JUCE and Julia source only.
- **Julia:** not executed. No Julia binary was available, and the pinned revision is newer than any release. Released Julia versions documented thread-local behaviour.
- **JUCE:** not built. Whether DAW hosts set FTZ/DAZ before invoking plug-in callbacks, or rely on plug-ins to do so, is not examined.
- **LLVM pinned revision:** not built. Execution used LLVM 19.1.7 and 21.1.8 with string attributes. That the first-class attribute keeps the same inliner behaviour is derived from source, not observed.
- **Clang `-ffast-math` attribute mismatch:** observed only in Clang 19.1.7. The upstream intent and later releases were not examined. This is not claimed as a bug.
- **GCC releases before 13:** behaviour with `-shared` was not executed here. It is taken from the commit and the bug record.
- **Schwarz, Schmookler and Trong (2005):** the full text is paywalled and was not examined. The abstract is qualitative only ("Traps to software can result in long execution times"; "With a small amount of additional hardware, denormalized numbers and underflows can be handled close to the speed of normalized numbers"). No cost figure from that paper is reported here.
- **Di Franco et al. (2017):** the full paper was not examined. Whether it discusses control state, rounding modes or fast-math beyond the slides is unknown.
- **Performance:** the subnormal penalty is measured for one operation (`mulsd`) on one CPU model under KVM. Other operations, AVX-512 vector forms, other microarchitectures and results that are subnormal from normal inputs were not measured. The cycle conversion assumes the nominal clock.
- **Fortran beyond gfortran:** other Fortran processors were not examined, including whether any of them protects procedures that do not use the IEEE modules.
- **Attractive but unsupported:**
  - "Every Fortran call boundary restores the rounding mode." This is false for gfortran when a non-IEEE-module procedure calls code that changes the mode.
  - "`-ffast-math` shared libraries no longer change MXCSR." This holds for GCC 13 and later, and for the Clang 19 build tested, without `-mdaz-ftz`. It does not hold for older binaries already in the field.
  - "LLVM prevents mixing denormal modes." LLVM only prevents *inlining* across incompatible modes.

## Evidence

All observations were made on 2026-11-21 (UTC). The source revisions are listed in `REPORT.json`.

**Standards and documentation.**
- Fortran 2023 draft J3/23-007r1, `j3-fortran/j3-papers@f052dca4c3d110465e3594b11c70dbc5c858d8fa:papers/23-007r1.pdf` (SHA-256 in `REPORT.json`):
  - 17.1 p. 464; 17.3 p. 466; 17.4–17.5 p. 468; 17.6–17.7 p. 469; 18.10.3 p. 531.
  - The quotes were checked with `pdftotext -layout`.
  - The F2018 draft 18-007r1 has the same wording at pp. 433–438 and 496.
- C11 committee draft N1570: 5.1.2.3p5, 7.6p1–3, 7.6.1p2, F.8.3, J.1. Read from an HTML rendering, so no page numbers are given.
- POSIX.1-2017, `pthread_create` DESCRIPTION and CHANGE HISTORY; the `sigaction` page; XSH 2.4. DOI `10.1109/IEEESTD.2018.8277153`, checked against Crossref.
- System V AMD64 psABI 1.0, `low-level-sys-info.tex` on the `master` branch of `gitlab.com/x86-psABIs/x86-64-ABI`. Sections read: "Registers", the "Register Usage" table, "Special Registers", "Thread State". A GitLab commit identifier could not be retrieved with the tools available, so the version string is the strongest identity.
- `MicrosoftDocs/cpp-docs@c40d993acf8dd1cc106257d11654f8dd1b761944:docs/build/x64-calling-convention.md:167-214, 216-220`.
- `ARM-software/abi-aa@9f9e067e6c6a5d3c5c8326756500cdbd940b8ff7:aapcs64/aapcs64.rst:898-906` (release 2026Q3).

**Source.**
- `llvm/llvm-project@04e0e9cc603537fbc16685f872fba17f937f90ff`:
  - `llvm/docs/LangRef.md:2888-2938, 4352-4362`;
  - `llvm/include/llvm/IR/Attributes.td:28-47, 431, 452-492`;
  - `llvm/lib/IR/Attributes.cpp:2614-2660`.
  - History: commit `2502e3b7badc` (PR 174293, merged 2026-02-05).
- `gcc-mirror/gcc@2fb8a47c8d94b257575fb6294b218be8dc81a8a3`:
  - `libgcc/config/i386/crtfastmath.c:24-98`;
  - `gcc/config/i386/gnu-user-common.h:47-53`;
  - `gcc/fortran/trans-decl.cc:7325-7339, 8466-8470, 8610-8612`;
  - `libgfortran/ieee/ieee_helper.c:165-203`;
  - `libgfortran/config/fpu-387.h:430-455`.
  - History: commit `e54375d85d4a`.
- `torvalds/linux@5f22fb20497f4983094131f00a734362300d22d2`:
  - `arch/x86/kernel/signal.c:295-310`;
  - `arch/x86/kernel/fpu/core.c:558-562, 677-740, 849-874`;
  - `arch/x86/kernel/fpu/signal.c:205, 398-418, 462-473`;
  - `arch/x86/include/asm/fpu/types.h:72`.
- `juce-framework/JUCE@654bdbc7a9db0dae90849b44abe91f339e9f0768`:
  - `modules/juce_audio_basics/buffers/juce_FloatVectorOperations.h:202-241`;
  - `modules/juce_audio_basics/buffers/juce_FloatVectorOperations.cpp:1438-1562`;
  - the two template and example files cited in §7.
- `JuliaLang/julia@cd4dedb3b5da854aa9609126a54d82ed7dfbd3d7`:
  - `base/rounding.jl:298-327`;
  - `src/julia_internal.h:1583-1740`;
  - `src/task.c:518, 717, 1142-1143, 1262`;
  - `src/julia_threads.h:566`;
  - `src/gf.c:474-614`;
  - `src/processor.cpp:1064-1120`.
  - History: commit `b72cfb3c9e63` (2026-11-17), its NEWS.md entry and its message.

**Execution.**
- `support/probes/run_all.sh` builds and runs every probe. The recorded output is `support/outputs/run_all.txt`.
- Host: x86-64 KVM guest, Intel Xeon CPU family 6 model 106 (Ice Lake server), 2.60 GHz nominal; timings pinned with `taskset -c 5`.
- Medians are over 7 repetitions inside each binary. Ranges in §9 span the recorded run plus earlier identical runs on the same day:
  - chain subnormal 35.5, 36.0, 38.1, 39.7, 37.5 and 35.3 ns/op;
  - `fegetenv` pair 136.2, 140.0, 133.2 and 143.5 ns;
  - gfortran IEEE call 233.4, 237.3, 243.7 and 230.6 ns.

**Literature and field data.**
- Dolan-Gavitt, blog post dated 2022-09-06 (URL in `REPORT.json`).
- GCC bug 55522 (comments 0, 19, 22, 45, 48) and the GCC 13 release notes (`gcc.gnu.org/gcc-13/changes.html`, "General Improvements").
- These DOIs were checked against Crossref metadata on 2026-11-21:
  - Di Franco et al., `10.1109/ASE.2017.8115662`, pp. 509–519; the abstract was read via OpenAlex and the slides at the authors' site.
  - Schwarz et al., `10.1109/TC.2005.118`, vol. 54(7), pp. 825–836; abstract only.
  - Andrysco et al., `10.1109/SP.2015.44`, pp. 623–639; §II.C read in the authors' PDF.
- A mingw-w64 mailing-list patch dated 2026-10-18 ("winpthreads: Inherit the floating-point environment in new threads"), secondary.

## Revalidation

- **Whole-boundary behaviour on a Linux host:** run `WORK=$(mktemp -d) sh support/probes/run_all.sh` and compare it with `support/outputs/run_all.txt`. The discriminating lines are:
  - `new pthread` equal to `parent set`;
  - `in handler` equal to `0x1f80`/`0x037f`;
  - `after sigreturn` equal to `parent set`;
  - the four `dlopen` lines;
  - the Fortran lines `1024` and `0`;
  - `calls left after inlining = 1` for the `ps` callee.
- **LLVM rule drift:** at a new revision, inspect `def DenormalFPEnv` and the `CompatRule` and `MergeRule` lists in `llvm/include/llvm/IR/Attributes.td`, and `denormModeCompatible`/`checkDenormMode` in `llvm/lib/IR/Attributes.cpp`. With a build that uses the first-class attribute, port `support/probes/llvm/` by replacing the string attribute with `denormal_fpenv(preservesign)`.
- **GCC loader behaviour:** check `GNU_USER_TARGET_MATHFILE_SPEC` in `gcc/config/i386/gnu-user-common.h` for the `!shared` guard. Run `gcc -ffast-math -shared` followed by the `dlopen` probe.
- **gfortran scope rule:** search `gcc/fortran/trans-decl.cc` for `is_ieee_module_used` and its two uses. Run `support/probes/fortran_modes.f90`.
- **Linux signal and clone:** search `arch/x86/kernel/signal.c` for `fpu__clear_user_states`, and `fpu_clone` in `arch/x86/kernel/fpu/core.c` for the `minimal` branch and `save_fpregs_to_fpstate`.
- **Microsoft, psABI and AAPCS64 contracts:** reread the MXCSR/FPCSR sections, the psABI "Registers" and "Thread State" paragraphs, and the AAPCS64 FPSR/FPCR paragraph. These are short and stable.
- **Julia:** in `src/task.c`, search for `fpctrl`: four uses plus root-task initialization. Check the masking in `jl_fpctrl_get`. Running `test/rounding.jl` from that revision would provide the execution evidence this report lacks.
- **JUCE:** diff the `ScopedNoDenormals` constructor and destructor. A two-line probe that raises an exception flag inside the scope and reads MXCSR after it would confirm the flag erasure derived in §7.
