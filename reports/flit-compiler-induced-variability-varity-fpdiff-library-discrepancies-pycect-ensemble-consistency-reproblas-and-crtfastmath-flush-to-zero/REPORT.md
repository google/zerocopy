# Floating-point evaluation policy as semantics: compiler and startup-object defaults, measured variability (FLiT, Varity, FPDiff, pyCECT), and reproducible summation

## Summary

- **Evaluation policy changes values, and each part of it has its own scope.** These settings each change floating-point results by themselves:
  - contraction of `a*b+c` into a fused multiply-add (FMA);
  - excess intermediate precision;
  - fast-math rewrites;
  - flush-to-zero (FTZ) and denormals-are-zero (DAZ) state;
  - library-function accuracy;
  - reduction order.

  They act at different scopes. Contraction and excess precision are decided per expression or per translation unit, at compile time. FTZ/DAZ is per-thread hardware state that a startup object sets once for the whole process. Reduction order is decided by the run-time partitioning and by library algorithm choice.
- **GCC's contraction default depends on the language mode.** It is `-ffp-contract=fast` in GNU modes (the default `-std=gnu17`) and `off` in ISO modes such as `-std=c17`. Contraction only shows up when two further conditions hold: the target ISA has FMA (baseline x86-64 does not) and optimisation is on.
  - Measured on GCC 15.2.0, one source line `a*b+c` evaluates to `0` or `-0x1p-54` depending on `-march`, `-std` and `-O` alone.
  - GCC ignores `#pragma STDC FP_CONTRACT` (it warns under `-Wall`).
  - Clang defaults to `-ffp-contract=on`: fusion within one expression, honouring the pragma.
- **`-ffast-math`, `-Ofast` or `-funsafe-math-optimizations` at link time changes the floating-point environment of the whole process.** Without `-shared`, these options link `crtfastmath.o`, whose constructor sets MXCSR FTZ|DAZ.
  - Measured: code compiled **without** fast-math loses subnormal results when the executable is merely *linked* with `-ffast-math`.
  - A shared library built with `-mdaz-ftz` flips FTZ/DAZ for its host process at load time, including code that never opted in.
  - New threads inherit the creating thread's MXCSR, but clearing it in one thread does not affect the others.
- **Verified compilers pin the policy down and make relaxation explicit.** CompCert maps `float`/`double` to binary32/binary64, rounds to nearest-even, and forbids reassociation and contraction; FMA is available only through explicit built-ins. It does **not** fix C's evaluation order: its correctness theorem allows any legal order. Icing (CakeML) admits fast-math rewrites only under explicit `opt` scopes, with a nondeterministic semantics that the optimisers are proved to refine.
- **Empirical studies find policy-induced output changes frequently, and sometimes large.** Figures from the studies:
  - MFEM under FLiT: 6.0% (gcc), 1.8% (clang) and 49.8% (icpc) of runs varied, with relative errors up to 197% in one example.
  - Varity: 50,000 runs on POWER9/V100.
  - FPDiff: 655 disagreement instances among four special-function libraries, 125 unique bugs.
  - Climate model (CESM): FMA-enabled builds failed the ensemble consistency test in 77.2% (SUMMIT) and 92.2% (CHEYENNE, AVX2) of trials.
- **Reproducible summation removes order dependence at a modest cost, but only order dependence.**
  - Demmel–Nguyen: one reduction, reported 1.2–1.6× conventional summation.
  - Ahrens–Demmel–Nguyen: 6-word accumulator, about 9n flops plus 3n bitwise operations, one pass, one reduction.

  These methods do not remove differences caused by contraction, FTZ, library accuracy or fast-math rewrites inside the addends.

## Applicability

- **Compiler defaults and driver behaviour** (the option documentation, crtfastmath sources and link specs):
  - GCC at `gcc-mirror/gcc` `1c6bee45b4c3d9f2500430371ef61d9487a5b8e7`, the development head on 2026-11-20.
  - The GCC 15.2.0 release, `5115c7e447fc07457443df874bf57840e8316d5f`. The relevant files differ from head only in copyright years, apart from the reworded `-mdaz-ftz` paragraph shown below.
  - Clang at `llvm/llvm-project` `83a19504f5c56c3410a3cdfee036c1e687dce224`.
- **Execution probes** ran the distribution build GCC "15.2.0 (Debian 15.2.0-14)" with GNU ld 2.47 and glibc 2.43 on x86-64 Linux, on an Intel Xeon @ 2.60 GHz cloud VM (96 vCPUs) with FMA/AVX2. They characterise that compiler on that host only.
  - Distribution patches were not audited.
  - AArch64, POWER, GPU, MSVC, ICX/ICC and Clang were **not executed**; Clang behaviour is from its manual and driver source only.
- **CompCert** findings are from `lib/Floats.v` and the driver at `AbsInt/CompCert` `2685140bf72c959446981fb99b5e44a8975021bc`, plus Boldo et al. 2015, which describes CompCert 2.4. No CompCert binary was run.
- **PyTorch** findings are documentation (`docs/source/notes/randomness.md`, `numerical_accuracy.md`) at `pytorch/pytorch` `f37e6ed227cb8010651c6ee2fda26ec900cc88c9`. No PyTorch code was run.
- **Harness semantics** were read from source at the pinned revisions: FLiT (`27b6061b9d2302fa8c3252fe770287bb4d07905b`), Varity (`f5e04921d7d48ea6ba9f2d4d71ab8f1edbbadef9`), FPDiff (`2c35e44e6732f7275887b6042febc3b928607c1d`) and pyCECT (`0c3d19dfa9a07fd2a67a38a1a2a898f7f2e9f4b9`). Study numbers are quoted from the papers, whose tool versions predate these revisions.
- **Summation probe.** The summation probe uses NumPy 2.3.5 and CPython 3.13.15 (`math.fsum`). Its "reproducible" summation is a toy written for this report, not ReproBLAS.
- **Combination of subjects.** The report compares how these subjects specify, default, measure or remove the same class of value changes. It does not claim the tools interoperate.

## Findings

### 1. Policy dimensions and their scope

| Dimension | Who decides | Scope of effect | Visible to a caller that did not opt in? | Basis |
|---|---|---|---|---|
| FMA contraction of `a*b+c` | compiler flag, language mode, target ISA, optimisation level, `FP_CONTRACT` pragma (Clang only) | expression (`on`) or across statements (`fast`) within the compiled TU | yes, through the values returned by the contracted function | normative + documentation + execution |
| Excess precision (x87) | target (`-m32`, `-mfpmath`), `-fexcess-precision`, language mode | expression / assignment within the TU | yes, through returned values (finite vs `inf` below) | documentation + execution |
| Fast-math rewrites (reassociation, reciprocal, finite-math, no signed zeros) | `-ffast-math`, `-funsafe-math-optimizations`, `-ffp-model=fast/aggressive` | TU (or function, via attributes) | yes, through returned values | documentation |
| FTZ/DAZ (MXCSR on x86, FPCR.FZ on AArch64) | `crtfastmath.o` constructor, linked by the driver; `-mdaz-ftz`; explicit `ldmxcsr` | **per thread**, initialised **process-wide** at startup or library load; inherited by threads created afterwards | **yes**: all code in the process, including TUs compiled without fast-math | source + execution |
| Library function accuracy | libm / special-function library version | every call site | yes | documentation (Monniaux; FPDiff) |
| Reduction order | thread count, partitioning, library algorithm selection (cuDNN benchmark mode) | run | yes | documentation + execution (toy) |

Basis: derived from the sections below. The "who decides" column of the FTZ/DAZ row shows that the actor flipping process state can be the final link step, or a shared library loaded later, rather than the author of the code that computes the value.

### 2. Normative baseline: C leaves contraction implementation-defined

The ISO C committee draft N1570 makes contraction implementation-defined (Basis: normative; read from a third-party HTML transcription because the official PDF could not be fetched):
- 6.5 p8: "A floating expression may be contracted ... Otherwise, whether and how expressions are contracted is implementation-defined."
- 7.12.2 p2: "The default state ('on' or 'off') for the pragma is implementation-defined."
- Footnote 90: "As contractions potentially undermine predictability, and can even decrease accuracy for containing expressions, their use needs to be well-defined and clearly documented."

Contraction across statements is therefore outside what the pragma governs. Clang's manual states that "Fusion across statements is not compliant with the C and C++ standards".

IEEE 754-2019 contents are not covered here. The clause list includes "9.2 Additional mathematical operations" and "11. Reproducible floating-point results" (clause 11 begins on p. 75), but the text of either clause was **not examined**. The IEEE background page says the 2019 revision recommends new `tanPi`, `aSinPi`, `aCosPi` operations and "augmented addition, subtraction, and multiplication operations [that] support ... reproducible reductions on arrays" (Basis: documentation).

### 3. GCC and Clang defaults (source and documentation)

GCC `gcc/doc/invoke.texi` at `1c6bee45b4c3d9f2500430371ef61d9487a5b8e7`:
- **Lines 13834–13846 (`-ffp-contract`).** "`-ffp-contract=on` enables floating-point expression contraction if allowed by the language standard. This is implemented for C and C++, where it enables contraction within one expression, but not across different statements. The default is `-ffp-contract=off` for C in a standards compliant mode (`-std=c11` or similar), `-ffp-contract=fast` otherwise." The 15.2.0 release has the same text at lines 12973–12974.
- **Lines 16507–16531 (`-fexcess-precision`).** "By default, `-fexcess-precision=fast` is in effect ... it is unpredictable when rounding to the types specified in the source code takes place." The `standard` setting "is enabled by default for C or C++ if a strict conformance option such as `-std=c99` ... is used", and "`-ffast-math` enables `-fexcess-precision=fast` by default regardless of whether a strict conformance option is used."
- **Lines 16555–16571 (`-ffast-math`).** It sets `-fno-math-errno -funsafe-math-optimizations -ffinite-math-only -fno-rounding-math -fno-signaling-nans -fcx-limited-range -fexcess-precision=fast`.
- **Lines 16592–16611 (`-funsafe-math-optimizations`).** "When used at link time, it may include libraries or startup files that change the default FPU control word". It enables `-fno-signed-zeros -fno-trapping-math -fassociative-math -freciprocal-math`.
- **Lines 13747–13756 (`-Ofast`).** It "turns on `-ffast-math`".
- **Lines 36738–36748 (`-mdaz-ftz`).** "`-Ofast`, `-ffast-math`, or `-funsafe-math-optimizations` options normally link in startup code that sets these flags except when building a shared library (`-shared`). You can use the `-mdaz-ftz` and `-mno-daz-ftz` options to explicitly enable or disable setting these flags, regardless of other options". The 15.2.0 text (lines 35836–35843) says the same in other words.

Clang `clang/docs/UsersManual.md` at `83a19504f5c56c3410a3cdfee036c1e687dce224`:
- **Lines 1842–1869 (`-ffp-contract`).**
  - `on` is the "default for languages other than CUDA/HIP", `fast` is the default for CUDA, and `fast-honor-pragmas` is the default for HIP.
  - "pragmas will be ignored with `-ffp-contract=fast`".
- **Lines 1998–2019 (`-ffp-model`).**
  - `precise` is the default and keeps `-ffp-contract=on`.
  - `strict` disables contraction and enables `FENV_ACCESS`.
  - `fast` and `aggressive` imply `ffp-contract=fast`.
- **Lines 2212–2223.** "`-ffast-math` and `-funsafe-math-optimizations` without the `-shared` option cause `crtfastmath.o` to be automatically linked, which adds a static constructor that sets the FTZ/DAZ bits in MXCSR, affecting not only the current compilation unit but all static and shared libraries included in the program."

The Clang driver logic is `clang/lib/Driver/ToolChain.cpp` lines 1868–1902, `ToolChain::isFastMathRuntimeAvailable` (Basis: source):

```cpp
  // Don't implicitly link in mode-changing libraries in a shared library, since
  // this can have very deleterious effects. ...
  bool Default = !Args.hasArgNoClaim(options::OPT_shared);
  ...
  if (!Args.hasFlag(options::OPT_mdaz_ftz, options::OPT_mno_daz_ftz, Default))
    return false;
  // If crtfastmath.o exists add it to the arguments.
  Path = GetFilePath("crtfastmath.o");
```

The rule above is: `-ffp-model` values other than `fast`/`aggressive`, and `-fno-fast-math`, turn the default off. With `-Ofast` those checks are skipped, so the default stays on unless `-shared` is given. `-mdaz-ftz`/`-mno-daz-ftz` override everything. Clang reuses GCC's `crtfastmath.o` when the file exists, so it never supplies the object itself. On a system without GCC's runtime objects, no FTZ constructor is linked, whatever the flags.

### 4. crtfastmath mechanics (GCC source)

`libgcc/config/i386/crtfastmath.c` at `1c6bee45b4c3d9f2500430371ef61d9487a5b8e7`, lines 25–26 and 82–96. The file is identical in 15.2.0 except for the copyright year.

```c
#define MXCSR_DAZ (1 << 6)	/* Enable denormals are zero mode */
#define MXCSR_FTZ (1 << 15)	/* Enable flush to zero mode */
...
static void __attribute__((constructor))
set_fast_math (void)
{
...
  unsigned int mxcsr = __builtin_ia32_stmxcsr ();
  mxcsr |= MXCSR_DAZ | MXCSR_FTZ;
  __builtin_ia32_ldmxcsr (mxcsr);
```

On 32-bit x86, the code first checks CPUID for SSE and probes DAZ support via `fxsave` (lines 28–80).

The link rule is `gcc/config/i386/gnu-user-common.h` lines 49–53:

```c
#define GNU_USER_TARGET_MATHFILE_SPEC \
  "%{mdaz-ftz:crtfastmath.o%s;Ofast|ffast-math|funsafe-math-optimizations:%{!shared:%{!mno-daz-ftz:crtfastmath.o%s}}} \
   %{mpc32:crtprec32.o%s} \
   %{mpc64:crtprec64.o%s} \
   %{mpc80:crtprec80.o%s}"
```

The AArch64 equivalents are:
- `gcc/config/aarch64/aarch64-linux.h` lines 58–59: `"%{Ofast|ffast-math|funsafe-math-optimizations:%{!shared:crtfastmath.o%s}}"`.
- `libgcc/config/aarch64/crtfastmath.c` lines 24–36: the constructor writes `_FPU_FPCR_FZ` (`0x1000000`) to FPCR, with the comment "Flush to zero, round to nearest, IEEE exceptions disabled". It **overwrites** the whole FPCR rather than OR-ing in one bit.

The AArch64 spec has no `-mdaz-ftz` override. Basis: source; AArch64 behaviour was not executed.

### 5. Measured on GCC 15.2.0 (x86-64)

All three probes are in `support/` and print exactly the lines quoted. Basis: execution (real compiler, small kernels written for this report).

**Contraction** (`support/contract.c`, `support/run_contract.sh`, output `support/contract.out`):
- The inputs are `a = 1+2^-27`, `b = 1-2^-27`, `c = -1`. The exact product `1-2^-54` rounds to `1.0`, so unfused evaluation gives `0` and fused evaluation gives `-2^-54`.
- `f` computes `a*b+c` in one expression; `g` uses `t=a*b; return t+c;`.

| Flags | FMA instructions in f / g | f | g |
|---|---|---|---|
| `-O2` (baseline x86-64, no FMA in ISA) | 0 / 0 | `0x0p+0` | `0x0p+0` |
| `-O2 -march=haswell` (default `gnu17` → `fast`) | 1 / 1 | `-0x1p-54` | `-0x1p-54` |
| `-O2 -march=haswell -std=c17` (→ `off`) | 0 / 0 | `0x0p+0` | `0x0p+0` |
| `-O2 -march=haswell -ffp-contract=on` | 1 / 0 | `-0x1p-54` | `0x0p+0` |
| `-O2 -march=haswell -ffp-contract=off` | 0 / 0 | `0x0p+0` | `0x0p+0` |
| `-O2 -march=haswell` + `#pragma STDC FP_CONTRACT OFF` | 1 / 1 | `-0x1p-54` | `-0x1p-54` |
| `-O0 -march=haswell` | 0 / 0 | `0x0p+0` | `0x0p+0` |
| `-O2 -march=haswell -std=c17 -ffast-math` | 1 / 1 | `-0x1p-54` | `-0x1p-54` |

The pragma row produced `warning: ignoring '#pragma STDC FP_CONTRACT' [-Wunknown-pragmas]`. Monniaux (2008, §4.3.1) reported the same for gcc 4.1.1 ("ignores the pragma with a warning"); the behaviour is unchanged in GCC 15.2.0. The `-O0` row shows that, in GNU mode, optimisation level alone flips the result. Both observations match the documentation in §3.

**Excess precision** (`support/excess.c`, `support/run_excess.sh`, output `support/excess.out`). The kernel computes `1e308*10/100`: `h` in one expression, `k` with the product first assigned to a `double`.

| Flags | `FLT_EVAL_METHOD` | h | k |
|---|---|---|---|
| `-m32 -O2` (x87, `fast`) | 2 | `1e+307` | `1e+307` |
| `-m32 -O2 -std=c17` (x87, `standard`) | 2 | `1e+307` | `inf` |
| `-m32 -O2 -fexcess-precision=standard` | 2 | `1e+307` | `inf` |
| `-m32 -O2 -msse2 -mfpmath=sse` | 0 | `inf` | `inf` |
| `-O2` (x86-64) | 0 | `inf` | `inf` |

These results show three things:
- Even in the `standard` mode, C permits the unassigned expression to keep x87 range.
- Only the assignment forces rounding.
- In GNU mode, rounding is "unpredictable", in the manual's word: here the overflow vanished.

This reproduces the `(v*v)/v` example of Monniaux §3.1.1 on a current compiler.

**FTZ/DAZ** (`support/half.c`, `support/ftzmain.c`, `support/ftzlib.c`, `support/run_ftz.sh`, output `support/ftz.out`):
- `half.c` (`x*0.5`, `x*2^100`) is compiled **without** fast-math in every row. For row 2, the objects are compiled without any fast-math option and only the final link adds `-ffast-math`.
- The results printed are `half(2^-1022)` and `scale_up(2^-1060)`.
- `gcc -###` showed `crtfastmath.o` on the link line for `-ffast-math`, `-Ofast`, `-funsafe-math-optimizations` and `-mdaz-ftz -shared`. It was absent for no flag, `-ffast-math -shared` and `-ffast-math -mno-daz-ftz`.

| Configuration | MXCSR at `main` | half(2^-1022) | scale_up(2^-1060) |
|---|---|---|---|
| 1. no fast-math anywhere | `0x1f80` (FTZ=0, DAZ=0) | `0x0.8p-1022` | `0x1p-960` |
| 2. objects compiled normally, executable **linked** with `-ffast-math` | `0x9fc0` (FTZ=1, DAZ=1) | `0x0p+0` | `0x0p+0` |
| 3. linked with `-ffast-math -mno-daz-ftz` | `0x1f80` | `0x0.8p-1022` | `0x1p-960` |
| 4. plain executable `dlopen`s a library built with `-ffast-math -shared` | `0x1f82` after load | `0x0.8p-1022` | `0x1p-960` |
| 5. plain executable `dlopen`s a library built with `-mdaz-ftz -shared` | `0x9fc2` after load | `0x0p+0` | `0x0p+0` |
| 6. executable linked against the `-mdaz-ftz` library, default link options | `0x1f80` (library dropped from `DT_NEEDED`) | `0x0.8p-1022` | `0x1p-960` |
| 7. same, with `-Wl,--no-as-needed` | `0x9fc0` (library constructor ran before `main`) | `0x0p+0` | `0x0p+0` |

Thread behaviour, in rows 2 and 5:
- A thread created afterwards started with FTZ=1 and DAZ=1, so MXCSR is inherited at creation.
- After that thread cleared both bits with `ldmxcsr`, its own results returned to `0x0.8p-1022` / `0x1p-960`.
- The main thread still had FTZ=1 after `join`.

FTZ/DAZ is therefore per-thread state with copy-on-create semantics. Whether it is set is a property of the link and load graph, not of the code computing the value. In row 6, the toolchain's default link options removed the unused library from `DT_NEEDED`, so its constructor never ran. Whether the process was flushed thus also depended on `--as-needed`.

### 6. Verified-compiler semantics

**CompCert, source** (`lib/Floats.v` at `2685140bf72c959446981fb99b5e44a8975021bc`; Basis: source):
- Line 31 is `Definition float := binary64.`
- Lines 282–291 define `add`, `sub`, `mul`, `div` and `fma` as Flocq `Bplus/Bminus/Bmult/Bdiv/Bfma 53 1024 ... mode_NE`, i.e. binary64 with round-to-nearest-even. The single-precision module (lines 1057–1066) mirrors this with `24 128`.
- Commutativity is proved only under a NaN side condition. Lines 356–360 read: `Theorem add_commut: forall x y, is_nan _ _ x = false \/ is_nan _ _ y = false -> add x y = add y x.` NaN payload propagation is architecture-dependent (`Archi.choose_nan_64`).
- The driver documents `-ffloat-const-prop <n>`, where 0 means none, 1 limited and 2 full (the default) (`driver/Driver.ml` lines 197–198; `driver/Clflags.ml` line 27).
- On x86, `x86/CBuiltins.ml` declares `__builtin_fmadd` and `__builtin_fmsub`.

**CompCert, as described by Boldo et al. 2015** (authors' manuscript, §3.3, CompCert 2.4; Basis: documentation):
- "Reassociation of FP operations, or 'contraction' of several operations into one (e.g. a multiply and an add being contracted into a fused multiply-add) are prohibited."
- "CompCert makes FMA instructions available as compiler built-in functions, but they must be explicitly used by the programmer."
- "All intermediate FP results in expressions are computed with the precision that corresponds to their static C types."
- Conversions "always round the FP value to the given FP type".
- "The CompCert formal semantics makes no provisions for programmers to change rounding modes at run-time."
- Constant propagation, literal parsing and bit-level conversion are verified (§6.1). The only verified FP rewrites are division by a power of two becoming multiplication and `x ⊗ 2.0 → x ⊕ x` (§6.2).
- Evaluation order is not fixed: "a C program can have several legal behaviors, owing to underspecification in expression evaluation order, and the compiler is allowed to pick any one of them."

**Icing** (Becker et al., CAV 2019; Basis: documentation):
- "floating-point semantics are relaxed only for expressions under an [opt] scope".
- Values are kept as trees, and rewrites, which include FMA introduction, commutativity, associativity, distributivity and NaN-check removal, are applied nondeterministically.
- The paper verifies three optimisers in HOL4: a strict one that "provably preserves IEEE 754 semantics", a greedy one (Theorem 1: optimising greedily equals applying the rewrites in the semantics), and a conditional one whose assumptions are "logged by the compiler".
- A deterministic, optimisation-free Icing execution is proved equivalent to CakeML source semantics. The backward direction requires well-typed programs.
- CakeML "does not support mapping fma's to hardware instructions" at the time of the paper.

**Pitfalls each design addresses** (Monniaux 2008 versus the designs above; Basis: derived):

| Monniaux pitfall | CompCert | Icing | GCC defaults |
|---|---|---|---|
| x87 excess precision / spill-dependent rounding (§3.1.1) | excluded: x87 is not modelled; SSE2 only | n/a (CakeML word semantics) | admitted in GNU mode on 32-bit x86 (measured, §5) |
| double rounding (§3.1.2) | excluded (no extended format) | n/a | admitted with x87 |
| FMA contraction (§3.2) | excluded unless the programmer writes the built-in | admitted only inside `opt` scope | admitted by default in GNU mode when the ISA has FMA (measured) |
| reassociation / vectorised sums (§4.3.2) | excluded | admitted only inside `opt` scope | admitted only with fast-math / unsafe-math |
| flush-to-zero (§3.1.3) | not modelled; the semantics assumes IEEE gradual underflow | not addressed in the text read | set process-wide by `crtfastmath.o` when linked with fast-math options |
| library functions (§4.1) | outside the semantics (external calls) | outside | outside |
| compile-time evaluation vs run-time modes (§4.3.1) | verified constant folding, round-to-nearest only | not examined | default `-fno-rounding-math` assumes round-to-nearest; `-frounding-math` "is experimental and does not currently guarantee to disable all GCC optimizations that are affected by rounding mode" (`invoke.texi` lines 16691–16711) |
| ignored `FP_CONTRACT` pragma (§4.3.1) | n/a (no contraction) | n/a | still ignored in 15.2.0 (measured) |

### 7. Deep-learning framework switches (PyTorch documentation)

At `f37e6ed227cb8010651c6ee2fda26ec900cc88c9` (Basis: documentation):
- **`randomness.md` lines 5–7.** "Completely reproducible results are not guaranteed across PyTorch releases, individual commits, or different platforms. Furthermore, results may not be reproducible between CPU and GPU executions, even when using identical seeds."
- **Lines 73–93.** cuDNN benchmarking "may select different algorithms on subsequent runs, even on the same machine". Setting `torch.backends.cudnn.benchmark = False` makes the selection deterministic.
- **Lines 96–99 and 140–146.** `torch.use_deterministic_algorithms(True)` selects deterministic implementations and raises an error for ops without one. `torch.backends.cudnn.deterministic = True` "controls only this behavior". Both are process-global switches. Per-device and per-thread scope was not examined.
- **`numerical_accuracy.md` lines 8–18.** The docs warn that floating-point addition and multiplication "are not associative", so "PyTorch is not guaranteed to produce bitwise identical results for floating point computations that are mathematically identical".
- **Lines 108–131 (TF32).** "By default, TF32 tensor cores are disabled for matrix multiplications and enabled for convolutions"; TF32 reads "only the first 10 bits of the input mantissa".
- **Lines 139–159.** Reduced-precision reduction for BF16 GEMMs "is turned on by default".

The deep-learning defaults are therefore mixed. Convolutions use a lower-precision mode by default and matrix multiplications do not; determinism is opt-in.

### 8. What each harness counts as "different"

Each harness below has its own oracle, so the study numbers in §9 are not directly comparable. Basis: source.

| Tool | "Different" means | Ground truth / baseline | Source |
|---|---|---|---|
| FLiT | `compare()` returns non-zero. Scalars: `flit::abs_compare` (absolute error); vectors: `flit::l2norm`; strings: always `0` by default | `ground_truth` build `g++ -O0` with no switches (default config) | `src/flit/TestBase.h` lines 363–389; `scripts/flitcli/config/flit-default.toml.in` lines 126–143 |
| Varity | the printed `%.17g` strings differ across compiler/optimisation configurations | none (pairwise comparison of configurations) | `README.md` (results.json format); `varity/varity.py` lines 41–64 |
| FPDiff | `2*|a-b|/(|a|+|b|) > ERROR_TOLERANCE = 0.001` between function synonyms, or a mix of exceptions, special values and doubles | none (consensus among libraries) | `workspace/header.py` lines 48–49, 548–600 |
| pyCECT | at least `minPCFail` (3) principal components each exceed `sigMul`·σ in at least `minRunFail` (2) of the new runs | an ensemble (default `esize` 1800 in `pyEnsSum.py` line 38) of perturbed-initial-condition runs | `pyCECT.py` lines 44–49, 100–110; `pyEnsLib.py` lines 1623, 1635, 1649 |

Details:
- **FLiT.**
  - The default search space is 4 optimisation levels × 17 switches (including none) = 68 g++ compilations, 4 × 18 = 72 for clang++, and 4 × 27 = 108 for icpc. This is computed from `flit-default.toml.in`.
  - The default `dev_build` uses `-O2 -funsafe-math-optimizations`.
  - `flit_bisect.py` `bisect_search` (lines 924–947) documents "complexity O(k*log(n))*O(score_func)", assuming that "all differing elements are independent", and checks that assumption with assertions.
- **Varity.**
  - `varity/cfg.py` defaults are 2 groups × 10 tests, 5 inputs per run, `REAL_TYPE = "double"` and `OPT_LEVELS = [("-O0", 1), ("-O0", 0), ("-O1", 0), ("-O2", 0), ("-O3", 0)]`.
  - The second tuple element selects the "nofma" variant: `-ffp-contract=off` for gcc/clang, `--fmad=false` for nvcc, `-qfloat=nomaf` for xlc, `-nofma` for PGI (`varity.py` lines 41–64).
  - gcc and clang are always passed `-std=c99`. Under GCC's documented default (§3), gcc's contraction is already `off` in that mode, so gcc's `O0_nofma` and `O0` variants coincide by construction. The Varity paper reports "no variations at all between -O0 and -O0_nofma for gcc" (Basis: derived + documentation).
- **FPDiff.**
  - Zero signs are not distinguished. Two zeros skip the relative-error test (`header.py` line 590), so `+0` versus `-0` is "consistent".
  - The branch intended for all-negative-zero outputs is `np.array([x is np.NZERO for x in outputs]).prod()` (line 579). It uses object identity, which is false for computed floats. Under NumPy ≥ 2.0 the attribute itself is gone: executing `np.NZERO` on NumPy 2.3.5 raises `AttributeError: np.NZERO was removed in the NumPy 2.0 release. Use -0.0 instead.`
  - The artifact targets an Ubuntu 18.04 / Python 3.6 / SciPy 1.3.1 environment (`Dockerfile`, `README.md` lines 17–20), where the attribute existed. This is a portability hazard for re-running the artifact, not evidence that the published results are wrong (Basis: source + execution).
- **pyCECT.**
  - `sigMul` defaults to 2.23 for the CAM model with 128 PCs, and to 2 with 26 PCs for MPAS (`pyCECT.py` lines 100–110).
  - `check_falsepositive` (`pyEnsLib.py` lines 1961–1993) hard-codes false-positive rates only for `nPC=50, sigMul=2, minPCFail=3, minRunFail=2, numRunFile=3` (`fp[0]=0.30305` ... `fp[4]=5e-05`), and returns `1.0` for any other parameters. Its only reference among the repository's top-level Python files is a commented-out call at `pyEnsLib.py` line 1644.

### 9. Empirical studies: frequency, size, causes

| Study | Subjects and configurations | Reported frequency | Reported magnitude | Attributed causes | Basis |
|---|---|---|---|---|---|
| FLiT (Sawaya et al., IISWC 2017) | litmus tests; GCC 5.2, Clang 3.8, Intel 16.0, CUDA 7.5; one optimisation level × one FP flag (about 50 flags) | aggregate fraction not reported (heat maps) | "up to four different values" for static code; Shewchuk summation "becomes as bad as the naïve implementation" under GCC `-funsafe-math-optimizations` | GCC aggressive mainly under unsafe-math; icpc "most aggressive"; Clang least | documentation |
| Bentley et al. (HPDC 2019) | MFEM: 244 compilations × 19 examples = 4,636 runs; gcc 8.2.0, clang 6.0.1, icpc 18.0.3 | variable runs: gcc 78/1,288 (6.0%), clang 24/1,368 (1.8%), icpc 984/1,976 (49.8%); 1,086 variant compilations in total | 183%–197% relative error (example 13); Laghos under xlc −O2→−O3: 11.2% in one iteration | FMA, AVX2, higher-precision intermediates; an undefined-behaviour swap macro; an exact comparison to 0.0 | documentation |
| Varity (Laguna, IPDPS 2020; preprint read) | 50,000 runs (25,000 FP64 + 25,000 FP32), POWER9 + V100; gcc 7.2, clang 8.0, xlc 16.01, nvcc 9.2 | per-mode tables carry a "scaled up by ×10^2" note, so they are not restated here | "zero versus 1e+300, or ... NaN versus 0.1, even for unoptimized code" | xlc emits FMA "even when ... -O0"; disabling FMA removes the example differences | documentation |
| FPDiff (Vanover et al., ISSTA 2020; abstract and artifact read) | GSL 2.6, SciPy 1.3.1, mpmath 1.1.0, jmat | 126 equivalence classes (95.8% precision, 79.0% recall); 655 disagreement instances, 150 of which represent 125 unique bugs; 30 fixed | categories in the artifact's frozen log: 327 exceptions/special values, 129 mixed, 94 doubles-from-inf, 61 inaccuracies, 23 doubles-from-NaN, 20 timeouts (total 654, one fewer than the abstract's 655; the artifact README warns of off-by-one differences caused by a flaky SciPy `hyperu` and by timeout detection) | special-value handling dominates; inaccuracies are a minority | documentation + source |
| CESM-ECT (Baker et al., GMD 2015) | 151-member ensemble, 120 variables, 1-year runs; Intel 13.1.2 −O2 default | NO-OPT, INTEL-15, PGI, GNU 4.8.0 pass; MIRA, BLUEWATERS, EOS fail near threshold (4–5 PCs); INTEL15-O3 fails with 38 PCs | false-positive target 0.5% with mσ=2, 3 runs, 3 PCs, 2 runs | found a big-endian-only bug in a stochastic cloud generator | documentation |
| UF-CAM-ECT (Milroy et al., GMD 2018) | nine time steps, 350-member ensemble | SUMMIT with FMA fails 77.2%; CHEYENNE with AVX2 fails 92.2%; both pass with the feature disabled | about 70× cheaper in CPU time than 12-month runs | FMA / AVX2; some slow or coupled effects are missed (CPL_BUG 0.1% vs 41.6% for CAM-ECT) | documentation |
| Ahn et al. (CACM 2021) | summary of FLiT and CESM-ECT | — | MFEM "as much as 190%" | FMA with the Intel 17 compiler flagged; 6 of more than 100 variables implicated | documentation |
| Pham et al. (ASE 2020) | 16 identical LeNet5 runs; WRN-28-10/CIFAR100 on TF 1.14, CUDA 10.0, cuDNN 7.6 | 83.8% of 901 surveyed practitioners unaware or unsure of implementation-level variance | implementation-level factors alone: up to 2.9% accuracy, 52.4% per-class accuracy, 145.3% training time | "nondeterminism-introducing" factors: algorithmic vs implementation-level (parallelism, auto-selected primitives, scheduling, FP precision) | documentation |
| Zhuang et al. (MLSys 2022, arXiv v1) | TF 2.4.1, CUDA 11, cuDNN 8; P100, V100, RTX5000, T4, TPUv2 | tooling alone: accuracy std from 0.05% to 0.91%; per-class std up to 23× top-1 std | deterministic kernels: 284%–746% (P100), 129%–241% (V100), 117%–196% (T4) **relative GPU kernel time** | cuDNN algorithm choice, accumulation order | documentation |

The Zhuang overheads are relative kernel-time ratios measured with `nvprof` (the paper reports 101% for MobileNet, i.e. about no overhead). They are not wall-clock time and not "+746%".

**Upstream preserved data: Varity's CUDA examples** (Basis: derived from upstream data; script `support/varity_cuda_classify.py`, output `support/varity_cuda_classify.out`):
- `cuda_examples/outputs.txt` holds 500 inconsistent cases produced with CUDA 9.2 (SHA-256 `97806af88e657249e790cfec5a6cf098080347d8ef53147685b00c0b8979cd88`).
- In 499 cases, `-O0..-O3` and `-O0 --fmad=false` agree and only `-O3 -use_fast_math` differs. In 196 of those, a single-precision subnormal became 0 (the flush-to-zero signature). The remaining cases involve NaN or ∞ appearing or disappearing, or changes between normal values.
- One case differs only under `--fmad=false`, and it is a 0 vs −0 difference.
- The label `O3_strict`, not defined in the directory's README, equals `O3_nostrict` in all 500 cases.

The set was curated *because* it is inconsistent. It says which cause dominates among inconsistencies, not how often programs are inconsistent.

### 10. Reproducible summation: guarantees and cost

- **Demmel–Nguyen 2015** (abstract only, plus statements in Ahrens et al.; Basis: documentation):
  - Results are "reproducible independent of the order of summation" under round-to-nearest.
  - It uses one reduction of a six-double array per sum and costs about 7n flops for the default accuracy.
  - It runs "within a factor of 1.2 to 1.6 of the runtime of conventional summation", as cited by Ahrens et al.
  - Ahrens et al. note that the 2015 algorithms "could not handle exceptions, very large summands, or very large intermediate results".
- **Ahrens–Demmel–Nguyen 2020** (TOMS; Basis: documentation):
  - It uses a 6-word "binned number" accumulator: one read-only pass, one reduction, about 9n flops plus 3n bitwise operations.
  - "no overflows can occur until the final rounding". Its error bound "can be up to 2^29 times smaller" than recursive summation on ill-conditioned double inputs.
  - Summand-count limits are 2^64 (double) and 2^33 (single).
  - Bitwise reproducibility of NaN payloads is not guaranteed.
  - ReproBLAS dot/gemv/gemm timings are deferred to future work; they are **not** in this paper.
  - Vendor comparison: Intel MKL CNR costs "at most a factor of 2" but is not reproducible across data ordering or processor counts; cuBLAS is described as reproducible "because they use a deterministic order of summation".
- **Toy demonstration** (`support/summation_order.py`, output `support/summation_order.out`; Basis: execution, toy model, not ReproBLAS). The input is 2^20 doubles `N(0,1)·10^U(-6,6)` with a fixed seed. The reference is `math.fsum`.
  - 17 orderings (sequential, NumPy pairwise, 2–1024 contiguous chunks, 8 random permutations) gave **17 distinct results**, with errors from 69 to 26,267 ulp.
  - A toy pre-rounding sum rounds each addend to a grid fixed by the global maximum, so all partial sums are exact. It gave 1 distinct result over 6 orderings at 1, 2 and 3 levels. The 1-level error was about 2×10^9 ulp; at 2 levels the result equalled `fsum` for this input.
  - Using a **per-chunk** grid instead of the global one gave a different result (`equal=False`). The grid must be agreed globally, which is the role of the binned format's fixed exponent boundaries.
  - Single-thread timings on the host above, from three runs on a shared VM: `numpy.sum` 0.28–0.32 ms, sequential accumulate 2.8–2.9 ms, `math.fsum` 53–54 ms, toy 2-level 18–25 ms (about 60–90× `numpy.sum`). The preserved output is one of these runs. These characterise the toy and CPython/NumPy only.

**What reproducible summation would and would not remove** (Basis: derived):
- It removes order and partition dependence: the chunking and permutation rows above, cuBLAS/MKL thread-count variation, and the reduction component of Pham/Zhuang variance.
- It does not remove the following, because these change the addends or the operations rather than their order:
  - FMA contraction differences (§5, Varity, MFEM example 13);
  - FTZ (Varity CUDA cases);
  - excess precision;
  - library discrepancies (FPDiff);
  - fast-math reassociation *inside* the addend computations.

### 11. Performance and resource footprint across six levels

| Level | What is known | Basis |
|---|---|---|
| L1 authoring/maintenance | CompCert-style fixed semantics costs no per-program annotation; Icing requires `opt` scopes per region. Person-month or token figures: not measured | documentation / not measured |
| L2 toolchain build | CompCert 2.4 compile time "about 4 times as long as GCC 4.9.1" on the paper's integer-constant tests (Boldo et al.). Building GCC, Clang or CompCert itself: not measured | documentation |
| L3 compilation latency | not measured for any policy setting | not measured |
| L4 generated-code performance | FLiT: up to about 5× speed-up from `-O3` plus unsafe flags on litmus tests. MFEM best average speed-ups 1.097 (gcc unsafe), 1.042 (clang), 1.056 (icpc fast=2); 14 of 19 examples fastest with bitwise-reproducible builds. Laghos xlc −O3: 2.42× speed-up with an 11.2% result change. Reproducible summation: 1.2–1.6× (Demmel–Nguyen). Deterministic GPU kernels: up to 7.46× kernel time (P100). Toy pre-rounding: 2-level about 60–90× `numpy.sum` (toy, not representative) | documentation + execution (toy) |
| L5 verification/check cost | CESM-ECT: about 20 min to summarise 151 members on 42 cores; three 1-year runs per test. UF-CAM-ECT: about 70× cheaper. FLiT Bisect: about 30 executions on average on MFEM; 14 runs (40 min) to re-find the Laghos issue; LULESH injections 15 executions on average. FPDiff full run: "Approximately 4 hours" (artifact README) | documentation |
| L6 memory/footprint | Ahrens et al.: 6-word accumulator per sum. CESM high-resolution run: about 250,000 core-hours per simulated year (CACM). Binary-size effects of fast-math: not measured | documentation / not measured |

### 12. Human comprehensibility and model simplicity

- **C1, comprehension.** The measured cases each break *local* reasoning:
  - A value computed in `half.c` depends on the link line of another artefact (§5 row 2), or on a library loaded later (row 5), or on `--as-needed` (row 6).
  - A program's result depends on `-std` and `-O` (contraction), and on assignment versus expression (excess precision).
  - None of this is visible in the source text. GCC gives no diagnostic except for the ignored pragma, and only under `-Wall`.
  - Pass/fail diagnostics differ per harness (§8): absolute error, ℓ2 norm, string inequality, 10^-3 relative difference, or PCA scores. A cross-study "N% of builds differ" is therefore not one quantity.
- **C2, simplicity.** One invariant would subsume most of the special cases: a function's floating-point results are determined by its source and its declared evaluation policy. Under that invariant, the policy would be a **visible part of the interface**: a per-function or per-module annotation carried into the binary.
  - The current mechanisms realise it in several unrelated ways: compiler flags, the `FP_CONTRACT` pragma (ignored by GCC), function attributes, the startup object, `ldmxcsr` calls, and framework globals.
  - FTZ/DAZ is the outlier. It is the only setting whose scope is decided by the link and load graph rather than by the code that computes. The Clang driver comment ("Don't implicitly link in mode-changing libraries in a shared library, since this can have very deleterious effects") and GCC's `!shared` spec are both patches on that one mechanism.
  - CompCert and Icing show the two consistent designs: fix one policy (CompCert), or make relaxation an explicit, scoped, verified refinement (Icing). This is a derived design observation, not a tested proposal.

### 13. Validation of the mechanisms (V1–V4)

- **V1, specification adequacy.**
  - pyCECT validates its own test by targeting a 0.5% false-positive rate, and by checking expected-pass (compiler or −O0 changes) and expected-fail (parameter changes) suites.
  - UF-CAM-ECT revealed both directions of inadequacy: some slow coupled bugs are missed, and some small-scale changes are caught that the 1-year test misses.
  - FPDiff reports precision and recall of its synonym classes against a manual ground truth.
- **V2, compiler and lowering testing.** Varity is randomized differential testing across compilers. FLiT is configuration-space differential testing with bisection to the symbol. Bentley et al. validated Bisect with 4,376 injected LULESH changes: 2,690 exact finds, 984 indirect, 0 wrong, 0 missed, 702 not measurable.
- **V3, concurrency, crash and silicon.** Only thread inheritance of MXCSR was exercised (§5). Weak-memory, crash and silicon validation are not applicable to these mechanisms and were not examined.
- **V4, field and human validation.**
  - CESM-ECT found real bugs in the field: big-endian RNG, CICE5 errors, and FMA-induced discrepancies.
  - Pham et al.'s survey measured practitioner mental models: 83.8% unaware or unsure of implementation-level variance.

## Boundaries

- **Not examined.**
  - Clang, ICX/ICC, MSVC, NVCC, XL and AArch64 behaviour were not executed; Clang and AArch64 statements are from documentation and source only.
  - Whether `-mdaz-ftz` exists for AArch64: it is absent from the AArch64 spec shown, but other files were not searched.
  - GCC `__attribute__((optimize("fast-math")))` and `#pragma GCC optimize` scope.
  - glibc `fesetenv` interaction with thread creation beyond MXCSR inheritance.
  - Fortran and C++ language-mode defaults.
  - The PyTorch CPU denormal switch `torch.set_flush_denormal`.
  - The text of IEEE 754-2019 clauses 9.2 and 11.
  - The full text of Demmel–Nguyen 2015 and Vanover et al. 2020: abstracts and artifacts only.
  - The final IPDPS text of Varity: the preprint LLNL-CONF-793958 was read.
- **Unknown.**
  - The exact Varity per-mode percentages, because of the scaling note in the preprint tables.
  - Whether Debian patches alter any GCC behaviour measured here.
  - ReproBLAS dot/gemv/gemm overheads: no source read reports them.
- **Known not to apply.**
  - Reproducible summation does not remove contraction, FTZ, excess-precision or library differences (§10).
  - CompCert's guarantees do not cover evaluation order, external library calls, or non-default rounding modes. Boldo et al. say such programs "fall outside the perimeter of CompCert's semantic preservation results".
  - The Varity CUDA classification describes a curated set, not a population rate.
- **Unsupported.**
  - GCC does not support `#pragma STDC FP_CONTRACT` (ignored with a warning).
  - CompCert does not support `long double` as an extended format.
- **Not established.**
  - That FMA or fast-math "usually" changes scientific output. The frequencies above depend on each harness's oracle and on curated or study-specific workloads.
  - That deterministic GPU execution costs 7.46× wall-clock: the figure is a kernel-time ratio for one network shape.
  - The toy timings characterise only the toy.
- **L1, L2 (for GCC, Clang and CompCert), L3, and fast-math binary-size effects:** not measured.

## Evidence

Evidence was gathered on 2026-11-21 (UTC). The GitHub head revisions were resolved through the GitHub API on that date.

- **GCC** `gcc-mirror/gcc@1c6bee45b4c3d9f2500430371ef61d9487a5b8e7`:
  - `libgcc/config/i386/crtfastmath.c` lines 24–99;
  - `gcc/config/i386/gnu-user-common.h` lines 45–58;
  - `gcc/config/aarch64/aarch64-linux.h` lines 58–64;
  - `libgcc/config/aarch64/crtfastmath.c` lines 24–36;
  - `gcc/doc/invoke.texi` lines 13747–13756, 13834–13846, 16507–16611, 16691–16711 and 36738–36748.
- **GCC 15.2.0** `gcc-mirror/gcc@5115c7e447fc07457443df874bf57840e8316d5f` (tag `releases/gcc-15.2.0`): the same files. `invoke.texi` lines 12973–12974 and 35836–35843; `crtfastmath.c` and `gnu-user-common.h` differ only in copyright lines.
- **Clang** `llvm/llvm-project@83a19504f5c56c3410a3cdfee036c1e687dce224`: `clang/docs/UsersManual.md` lines 1652–1653, 1682–1687, 1771–1787, 1842–1869, 1998–2019 and 2212–2223; `clang/lib/Driver/ToolChain.cpp` lines 1868–1913.
- **CompCert** `AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`: `lib/Floats.v` lines 31, 155–160, 278–291, 356–375 and 1053–1066; `driver/Driver.ml` lines 195–199; `driver/Clflags.ml` line 27; `x86/CBuiltins.ml` lines 38–50.
- **PyTorch** `pytorch/pytorch@f37e6ed227cb8010651c6ee2fda26ec900cc88c9`: `docs/source/notes/randomness.md` lines 1–12, 73–99 and 140–146; `docs/source/notes/numerical_accuracy.md` lines 8–18 and 106–159.
- **FLiT** `PRUNERS/FLiT@27b6061b9d2302fa8c3252fe770287bb4d07905b`: `scripts/flitcli/config/flit-default.toml.in`; `src/flit/TestBase.h` lines 355–389; `scripts/flitcli/flit_bisect.py` lines 786–947.
- **Varity** `LLNL/Varity@f5e04921d7d48ea6ba9f2d4d71ab8f1edbbadef9`: `varity/cfg.py` lines 1–49; `varity/varity.py` lines 35–75 and 118–140; `cuda_examples/README.md`; `cuda_examples/outputs.txt` (SHA-256 above).
- **FPDiff** `ucd-plse/FPDiff@2c35e44e6732f7275887b6042febc3b928607c1d`:
  - `workspace/header.py` lines 29–49, 386–423 and 548–600;
  - `workspace/classify.py` lines 177–206;
  - `frozenState/full_logs/statistics.txt` and `README.md`;
  - `README.md` lines 8–20;
  - `Dockerfile` lines 1–14.
- **pyCECT** `NCAR/PyCECT@0c3d19dfa9a07fd2a67a38a1a2a898f7f2e9f4b9`: `pyCECT.py` lines 15–49 and 95–112; `pyEnsLib.py` lines 1607–1700 and 1961–1993; `pyEnsSum.py` lines 35–49.
- **Literature.** Every DOI was verified against Crossref metadata (title, authors, venue, year) on 2026-11-21, except Zhuang et al., which was verified via DBLP and the MLSys 2022 proceedings page (arXiv:2106.11872 v1).

  | Work | DOI or identifier | Version read |
  |---|---|---|
  | Monniaux | 10.1145/1353445.1353446 | arXiv cs/0701192v5, full text |
  | Demmel & Nguyen | 10.1109/TC.2014.2345391 | abstract |
  | Boldo et al. | 10.1007/s10817-014-9317-x | authors' manuscript, full text |
  | Baker et al. | 10.5194/gmd-8-2829-2015 | full text |
  | Sawaya et al. | 10.1109/IISWC.2017.8167780 | author copy |
  | Milroy et al. | 10.5194/gmd-11-697-2018 | full text |
  | Bentley et al. | 10.1145/3307681.3325960 | author camera-ready |
  | Becker et al. | 10.1007/978-3-030-25543-5_10 | open-access HTML |
  | Laguna | 10.1109/IPDPS47924.2020.00070 | preprint LLNL-CONF-793958 |
  | Vanover et al. | 10.1145/3395363.3397380 | abstract + artifact |
  | Pham et al. | 10.1145/3324884.3416545 | author copy |
  | Ahrens et al. | 10.1145/3389360 | publisher PDF |
  | Ahn et al. | 10.1145/3382037 | typeset article |
  | IEEE Std 754-2019 | 10.1109/IEEESTD.2019.8766229 | table of contents, clauses 1–2 via the identical ISO/IEC 60559:2020 preview, and the IEEE background page |
  | ISO C N1570 | — | §6.5 p8, §7.12.2, J.3, F.7, via an HTML transcription |

- **Execution environment.** x86-64 Linux; GCC 15.2.0 (Debian 15.2.0-14); GNU ld 2.47; glibc 2.43; Python 3.13.15; NumPy 2.3.5; Intel Xeon @ 2.60 GHz with FMA and AVX2. Commands and full outputs are in `support/` (`contract.out`, `excess.out`, `ftz.out`, `summation_order.out`, `varity_cuda_classify.out`). Each script writes temporaries under `${WORK:-/tmp/fp_probe_work}`.

## Revalidation

- **Compiler defaults.**
  - Run `support/run_contract.sh` and `support/run_excess.sh` with the target compiler.
  - Compare FMA counts and printed hex values with the tables in §5.
  - For a new GCC, `grep -n 'The default is @option{-ffp-contract' gcc/doc/invoke.texi`.
- **crtfastmath linkage.**
  - Run `gcc -### -ffast-math x.o 2>&1 | grep -c crtfastmath` (and with `-shared`, `-mno-daz-ftz`, `-mdaz-ftz -shared`).
  - Run `support/run_ftz.sh` and check rows 2, 5 and 7 for FTZ=1.
  - Diff `GNU_USER_TARGET_MATHFILE_SPEC` in `gcc/config/i386/gnu-user-common.h` and `ToolChain::isFastMathRuntimeAvailable` in Clang.
- **CompCert.** Diff `lib/Floats.v` definitions of `add`/`mul`/`fma` (the `mode_NE` argument), and run `ccomp --help | grep float-const-prop`.
- **PyTorch.** Re-read `randomness.md` and `numerical_accuracy.md`; check the TF32 default sentence and the `use_deterministic_algorithms` section.
- **Harness oracles.** Re-check these lines against §8:
  - FPDiff `ERROR_TOLERANCE`, and the `np.NZERO` line in `workspace/header.py`;
  - pyCECT defaults in `pyCECT.py` and the comparison in `comparePCAscores`;
  - FLiT `compare()` defaults in `TestBase.h`;
  - Varity `getExtraOptimization`.
- **Varity CUDA classification.** Run `python3 support/varity_cuda_classify.py outputs.txt` on the upstream file and compare its counts with §9.
- **Summation.** Run `python3 support/summation_order.py`. The distinct-result count and the per-chunk-grid inequality should reproduce; exact ulp values depend on the NumPy pairwise blocking.
- **Study numbers** need the papers. No cheaper check exists for them.
