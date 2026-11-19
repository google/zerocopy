# The C ABI as cross-language narrow waist: psABI prose, data-representation fossils, stack conventions, and what is actually irreducible

## Summary

Every mainstream language interoperates by degrading to the C view of a platform's processor-specific
ABI (psABI). That narrow waist has three properties a later engineer should retain.

1. **It is prose, re-implemented independently, and the implementations document their own
   disagreements.** The System V AMD64 psABI, the Microsoft x64 convention, and AAPCS64 are English
   rules plus a few worked examples. Clang, GCC, rustc, and libffi each carry a separate
   implementation (rustc's x86-64 classifier is "taken from the clay language"; libffi's must stay
   "identical to the code in gcc/config/i386/i386.c"). Divergences found, with sources below:
   - the psABI `va_arg` algorithm compared against `304 − num_fp·16` until an editorial fix in
     June 2024 (its commit message dates the slip to August 2001); Clang's source and GCC
     15.2.0's observed behaviour use 176;
   - Clang before version 24 assumed callers extend sub-`int` arguments to 32 bits, which the
     psABI never required (text sharpened March 2025; Clang now has
     `-msmall-int-abi-compat={platform,clang,both}`);
   - LLVM gave `i128` 8-byte alignment on x86 and could split an `__int128` argument between
     `r9` and the stack, both contrary to the psABI (fixed in LLVM 18, rustc 1.77/1.78);
   - Clang keeps five ABI-compatibility levels plus per-OS exemptions inside one x86-64
     classifier, with the source comment "gcc passes <1 x double> in memory. :(";
   - AAPCS64 leaves empty records unspecified, its `va_arg` pseudo-code carries an open review
     note, and Apple's variant changes at least three rules;
   - GCC 15.2.0's `ms_abi` emulation on Linux passes a 16-byte variadic struct by reference but
     its `va_arg` reads it by value (observed by execution; a likely cause was found by reading
     source and is not confirmed);
   - the psABI says plain bit-fields are non-negative, while GCC 15.2.0 reads a plain `int f:3`
     holding all ones as −1.
2. **One C type lands in three unrelated places.** `struct { double a; long long b; }` is passed in
   `xmm0`+`rdi` (System V), by pointer in `rcx` (Microsoft x64), or in `x0`+`x1` (AAPCS64);
   `__int128` in `rdi:rsi`, by pointer (returned in `xmm0` by GNU-family compilers), or in an
   *even-numbered* pair `x[2n]:x[2n+1]` (not on Apple platforms). The hidden result pointer uses
   up `rdi`, uses up the first positional slot `rcx`, or has the dedicated `x8`. All three — and
   Go's unrelated internal ABI — share one structural rule: an argument is never split between
   registers and stack.
3. **Most of the C data model is documented historical contingency; a short list is not.**
   NUL-terminated strings, array-to-pointer conversion, integer promotions whose results flip with
   the data model, implementation-defined bit-field allocation, and size-forgetting `free` each
   have a recorded origin and a living counterexample (Go's unstable register ABI, Swift's
   resilient witness-table ABI, the WebAssembly Component Model's executable Canonical ABI). What
   survives every counterexample: a finite register file, an agreed memory image wherever
   separately compiled parties share data, all-or-nothing argument placement, an agreed
   deallocation and cleanup protocol, and the need of precompiled native frames for a contiguous,
   non-moving stack — the reading offered here (finding 5.2, derived) for why Go switches
   stacks for cgo calls and Java pins virtual threads inside native frames.

The probe `support/verify_c_abi_contingencies.py` re-derives the classification, layout,
`va_list`, and integer-conversion results (80 model checks) and, on x86-64 Linux with a C
compiler, observes them at run time (45 checks with GCC 15.2.0).

## Applicability

**Subjects and how they relate.** The report compares three normative calling-convention texts —
the System V AMD64 psABI (LaTeX source at GitLab commit `e1ce0983…`, version macro 1.0), the
Microsoft x64 documentation (`MicrosoftDocs/cpp-docs` at `807f0a38…`), and AAPCS64 release 2026Q3
(`ARM-software/abi-aa` at `9f9e067e…`) — and reads four independent implementations *through* them:
Clang/LLVM (`ffcd0a52…`, a 24.0 development tree), rustc (`b0b60066…`, 1.102.0 development tree),
libffi (`de7afe7a…`, 3.8.1 development tree), and GCC 15.2.0 (upstream tag commit `5115c7e4…`
for source; the Debian build `15.2.0-14` for execution — a distribution build may carry patches
absent from the upstream tag, so source and execution evidence for GCC are related but not
identical subjects). Language rules come from the public C drafts N1570 (C11) and N3220 (first working draft after C23, self-labelled "ISO/IEC 9899:2024
(en)") — drafts, not the published ISO texts. History comes from Ritchie's HOPL-II paper. Swift,
Go, the Itanium C++ exception-handling ABI, the WebAssembly Component Model, Rust RFC 230, a Rust
blog post, the Go release notes, and JEP 444 serve as counterexample or postmortem evidence at
the revisions listed under Evidence.

**Scope of each kind of claim.**

- What a specification *requires* applies to that pinned text only.
- Statements about Clang, rustc, libffi, Swift, and Go come from **source or documentation at the
  pinned commit**; none was executed.
- **Execution** evidence exists only for GCC 15.2.0 (Debian 15.2.0-14) on x86-64 Linux: natively
  for System V, and through the `ms_abi` function attribute and `ms_struct` type attribute for the
  Microsoft rules — one compiler's emulation on a Linux host, not MSVC and not a Windows target.
- **AAPCS64 results are model-only**, derived from the specification's stage tables and cross-read
  against Clang, LLVM, libffi, and rustc source.
- Types covered: integers, pointers, `float`/`double`/`long double`, `__int128`, `__float128`,
  plain, packed, and empty structs (the last a GNU C extension), and the two vector types of the
  psABI's worked example. C++ classes, complex numbers, `_BitInt`, scalable vectors, and
  x32/ILP32 are outside the model.

**Relation to neighbouring packages in the same corpus.** This report is the language-neutral
layer and does not repeat Rust-specific material available elsewhere:
`tier1-calling-conventions-fnabi-and-llvm-lowering` (rustc's `FnAbi`/`PassMode` pipeline and LLVM
attribute lowering), `abi-cross-testing-matrix-rustc-llvm-cranelift-gcc-clang` (live caller ×
callee cross-compiler matrix and a catalogue of rustc/Clang/GCC mismatches),
`rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking` (`extern "C-unwind"` and unwinder
linkage), and `rust-stack-discipline-probes-red-zones-and-overflow` (rustc stack probes, red-zone
use, overflow handling). This report supplies the normative rule, its history, and the
other compilers' reading.

## Findings

### 1. Three prose conventions, side by side

| Property | System V AMD64 psABI | Microsoft x64 | AAPCS64 (2026Q3) |
| --- | --- | --- | --- |
| Integer argument registers | `rdi rsi rdx rcx r8 r9`, next-free | `rcx rdx r8 r9`, **by argument position** | `x0`–`x7`, next-free |
| FP/vector argument registers | `xmm0`–`xmm7`, independent counter | `xmm0`–`xmm3`, **same four positions** | `v0`–`v7`, independent counter |
| Aggregate rule | classify each *eightbyte* as INTEGER, SSE, SSEUP, X87, X87UP, COMPLEX_X87, NO_CLASS, or MEMORY; merge per eightbyte; more than two eightbytes ⇒ MEMORY unless one vector | size 1, 2, 4, or 8 bytes ⇒ by value in the integer slot; otherwise pointer to a caller-allocated, 16-byte-aligned copy | homogeneous FP/vector aggregate of ≤ 4 members ⇒ one `v` register each; other composites ≤ 16 bytes ⇒ `x` registers; larger ⇒ pointer to caller copy |
| Split between registers and stack | never; partial assignments "get reverted" | never; "A single argument is never spread across multiple registers" | never (rules C.11–C.13 set the register counter to 8) |
| 128-bit integer | two INTEGER eightbytes; 16-byte aligned when in memory | not a vendor type; GNU-family compilers pass by pointer and return in `xmm0` | two consecutive `x` registers starting at an **even** number (C.10) |
| Hidden result pointer | in `rdi` (uses up the first integer register); callee returns it in `rax` | first positional slot (`rcx`), other arguments shift right; returned in `rax` | dedicated `x8`; callee need not preserve it |
| Excess bits of narrow integers | unspecified; consumer extends; `_Bool` has 8 significant bits forming 0 or 1 | "the callee can ignore the upper bits"; unused return bits undefined | unspecified; "named integral values must be narrowed by the callee" |
| Stack alignment at a call | 16 bytes (32/64 with `__m256`/`__m512` on the stack) | 16 bytes outside prolog/epilog | `SP mod 16 = 0` |
| Memory below the stack pointer | 128-byte **red zone** usable by leaf code | none ("All memory beyond the current address of RSP is considered volatile"); instead 32 bytes of caller-allocated *home space* above the return address | none: "No thread is permitted to access … the inactive region" |
| Variadic calls | `al` = upper bound on vector registers used; `va_list` is a 24-byte record | FP values duplicated into the matching integer register; `va_list` is a pointer | `va_list` is a 32-byte, five-field record (Apple variant: all variadic arguments on the stack) |
| `long` / `long double` / plain `char` | 8 bytes / 80-bit x87 in 16 bytes / signed | 4 bytes / same representation as `double` / signed | 8 bytes (LP64; an LLP64 variant is defined) / IEEE binary128 / **unsigned** |

Consequences computed by the probe's model (one argument, then the same type as a return value;
`&r` = pointer in `r`, `stack@n` = byte offset in the outgoing argument area, `sret(r)` = hidden
result pointer in `r`):

| C type | System V arg / ret | Microsoft x64 arg / ret | AAPCS64 arg / ret |
| --- | --- | --- | --- |
| `struct { double a; long long b; }` | `xmm0+rdi` / `xmm0+rax` | `&rcx` / `sret(rcx)->rax` | `x0+x1` / `x0+x1` |
| `struct { float a, b, c, d; }` | `xmm0+xmm1` / `xmm0+xmm1` | `&rcx` / `sret(rcx)->rax` | `v0+v1+v2+v3` / same |
| `struct { double a, b, c, d; }` | `stack@0` / `sret(rdi)->rax` | `&rcx` / `sret(rcx)->rax` | `v0+v1+v2+v3` / same |
| `struct { long long a, b, c; }` | `stack@0` / `sret(rdi)->rax` | `&rcx` / `sret(rcx)->rax` | `&x0` / `indirect(x8)` |
| `struct { int a; float b; }` | `rdi` / `rax` | `rcx` / `rax` | `x0` / `x0` |
| `__int128` | `rdi+rsi` / `rax+rdx` | `&rcx` / `xmm0` | `x0+x1` / `x0+x1` |
| `long double` | `stack@0` / `st0` | `xmm0` / `xmm0` | `v0` / `v0` |
| `struct { char a, b, c; }` | `rdi` / `rax` | `&rcx` / `sret(rcx)->rax` | `x0` / `x0` |

Position matters as much as type:

```text
f(char pad, __int128 a, __int128 b, __int128 c, long long d)
  System V:  pad=rdi  a=rsi:rdx  b=rcx:r8  c=stack@0 (whole)  d=r9
f(int a, __int128 b)
  AAPCS64:   a=x0  b=x2:x3   (x1 skipped)        Apple arm64:  a=x0  b=x1:x2
```

The psABI's own worked example
`func(int e, int f, structparm s, int g, int h, long double ld, double m, __m256 y, __m512 z, double n, int i, int j, int k)`
with `structparm = { int a, b; double d; }` assigns `e`=`rdi`, `f`=`rsi`, `s`=`rdx`+`xmm0`,
`g`=`rcx`, `h`=`r8`, `ld`=stack 0, `m`=`xmm1`, `y`=`ymm2`, `z`=`zmm3`, `n`=`xmm4`, `i`=`r9`,
`j`=stack 16, `k`=stack 24. The model reproduces it; GCC 15.2.0 reproduces the subset without
the vector types at run time.

Basis: normative (psABI "Parameter Passing", "The Stack Frame", "Variable Argument Lists";
Microsoft "x64 calling convention", "x64 stack usage", "x64 software conventions"; AAPCS64
"Parameter passing rules", "Result return", "The Stack", type-mapping tables) + derived (locations
computed by the probe's model from those rules) + execution (System V rows and the Microsoft
rows for aggregates, `__int128`, and scalars observed with GCC 15.2.0; AAPCS64 not executed).

### 2. Documented divergences among independent implementations

Each row is a place where the prose, or two readings of it, disagreed; "Status" is as of the
pinned revisions.

| # | What the text says | Who diverged, and how it is known | Status |
| --- | --- | --- | --- |
| D1 | psABI `va_arg` step 3 compared `fp_offset` against `304 − num_fp·16` | psABI commit "va_arg: max fp_offset is 176" (2024-06-03): the draft once allowed all 16 XMM registers (`6·8+16·16`); the scheme changed in August 2001 "but failed to adjust the offsets in the va_arg machinery". Clang's source quotes 304 and adds "NOTE: 304 is a typo, there are (6 * 8 + 8 * 16) = 176 bytes of register save space" | Text fixed 2024. The 2001 date and the statement that no real compiler used 304 are the commit author's; here 176 was seen in Clang source and in GCC 15.2.0 execution only |
| D2 | Excess bits of INTEGER-class values "are unspecified" (psABI); the consumer must extend | Clang's option documentation: "In the past, Clang passed promotable integer arguments … using a parameter convention in which the caller was assumed to have sign-extended or zero-extended the argument to the width of an 'int'. This convention did not conform to the documented psABI". The psABI sentence was generalized from `_Bool` to all INTEGER types on 2025-03-12 | Clang default is `both` (caller extends, callee does not assume); Darwin and PlayStation are pinned to the old `clang` behaviour; rustc extends integer arguments to 32 bits itself and extends returned `bool` to 8 bits |
| D3 | `__int128` has 16-byte alignment and is passed whole in registers or whole in memory | LLVM's data layout gave `i128` 8-byte alignment on x86 (rustc 1.76: `align_of::<i128>() == 8`; GCC 13.2: 16; Clang 17: 16 only through a manual override), and LLVM passed an `i128` half in `r9`, half on the stack — reproduced in the Rust blog post with `foo(char, __int128, __int128, __int128)` under Clang 17 | Alignment patch landed October 2023, split fix alongside; both in LLVM 18; Rust 1.77 corrects alignment, 1.78 ships LLVM 18 |
| D4 | psABI revision 0.98 added two post-merge rules; later text classified more vector shapes | Clang's x86-64 classifier contains `honorsRevision0_98()` (false on Darwin), `classifyIntegerMMXAsSSE()` (false for Clang ≤ 3.8 compatibility, Darwin, PlayStation, FreeBSD), `passInt128VectorsInMem()` (not Clang ≤ 9; Linux and NetBSD only), `returnCXXRecordGreaterThan128InMem()` (not Clang ≤ 20), a Clang-11 union rule, a post-23 unnamed-bit-field rule, and the comment "gcc passes <1 x double> in memory. :(" | One function, at least five historical ABIs selectable by `-fclang-abi-compat` and target triple |
| D5 | psABI defines vectors only for the `__m64`/`__m128`/`__m256`/`__m512` shapes | libffi: narrower vectors "are unspecified, and GCC and Clang disagree on them … libffi cannot tell which convention the target function was compiled for, so it accepts only the shapes both compilers agree on"; everything else is `FFI_BAD_TYPEDEF` | A foreign-function library refuses types rather than guess |
| D6 | AAPCS64 does not mention empty records | Clang: "AAPCS64 does not say that empty records are ignored as arguments, but other compilers do so in certain situations, and we copy that behavior. Those situations are in fact language-mode-specific … Darwin overrides the psABI here"; and for zero-sized C++ arguments, "This isn't defined by any standard, so we copy GCC's behaviour" | Behaviour depends on C versus C++ mode and on the OS |
| D7 | AAPCS64 C.10 (even register), C.14/C.16 (8-byte stack slots), register save areas for variadics | LLVM: "Darwin uses a calling convention which differs in only two ways from the standard one at this level: i128s (i.e. split i64s) don't need even registers. Stack slots are sized as needed rather than being at least 64-bit"; its Darwin variadic convention is "Everything is on the stack". libffi carries the variants as `__APPLE__`/`_WIN32` conditionals ("The normal AArch64 ABI requires even Xreg; Darwin does not"), rustc as an `AAPCS`/`DarwinPCS`/`Win64` enum "to accommodate Apple and Microsoft's deviations" | Three AArch64 C ABIs under one architecture name |
| D8 | AAPCS64 `va_arg` pseudo-code | The specification's own review note: "The above pseudo code does not currently handle composite types that are passed by value, and where a copy is made and reference created to the copy. This will be corrected in a future revision" | Open in 2026Q3 |
| D9 | Microsoft x64 has no `__int128`, `__float128`, or zero-sized type | Clang: "Mingw64 GCC returns i128 in XMM0 … Clang matches them for compatibility"; "Mingw64 GCC returns f128 via sret, and Clang matches that". rustc: "`i128` is returned in xmm0 by Clang and GCC … This may change for the `-msvc` targets"; "Windows ABIs do not talk about ZST since such types do not exist in MSVC. However, clang and gcc allow ZST in their windows-gnu targets, and pass them by pointer indirection" | Convention defined by mutual imitation, not by the vendor text |
| D10 | Microsoft x64: arguments that are not 1, 2, 4, or 8 bytes are passed by reference, variadic or not | GCC 15.2.0 on Linux: a call to an `ms_abi` variadic function passes `struct { double; long long; }` by reference, but `__builtin_va_arg` on a `__builtin_ms_va_list` in the callee advances 16 bytes and yields garbage. Source: `std_gimplify_va_arg_expr` → `pass_va_arg_by_reference` calls the target hook with a null argument state, and `ix86_pass_by_reference` then selects `cum ? cum->call_abi : ix86_abi` — the target's *default* ABI, not the current function's | Present in the executed build; other GCC versions and Windows targets not examined |
| D11 | psABI: "Bit-fields that are neither signed nor unsigned always have non-negative values" | GCC 15.2.0 stores `0b111` in `struct { int f : 3; }` and reads back −1; Microsoft's C documentation states the opposite of the psABI outright: "Bit fields defined as `int` are treated as `signed`" | psABI text and the one GCC build executed disagree |

Bit-field *packing* is a second, independent axis. The psABI rule is: allocate right to left, a
field "must be contained in a storage unit appropriate for its declared type", and fields "may
share a storage unit with other struct / union members". Microsoft's rule is: "Adjacent bit fields
are packed into the same 1-, 2-, or 4-byte allocation unit if the integral types are the same size
and if the next bit field fits". Same declarations, different objects:

| Declaration body | psABI rule size / align | Microsoft rule size / align |
| --- | --- | --- |
| `unsigned char a:4; unsigned int b:4;` | 4 / 4 | 8 / 4 |
| `unsigned int a:4; unsigned char b;` | 4 / 4 | 8 / 4 |
| `unsigned int a:20; unsigned int b:20;` | 8 / 4 | 8 / 4 |
| `unsigned long long a:33; unsigned int b:10;` | 8 / 8 | 16 / 8 |

Basis: normative (psABI, AAPCS64, Microsoft texts) + source (Clang, LLVM, rustc, libffi, and GCC
files listed under Evidence) + documentation (psABI commit messages for D1/D2; Rust blog post for
D3) + execution (D10, D11, and the bit-field table under GCC 15.2.0 native layout and
`__attribute__((ms_struct))`; the probe's `a_i128x3` case confirms GCC's placement for D3) +
derived (D10's causal chain is inferred from reading three GCC functions together, not confirmed
with a debugger or a patched compiler).

### 3. Living counterexamples: ABIs that are negotiated, versioned, or executable

| Property | C psABIs | Go `ABIInternal` | Swift | Component Model Canonical ABI |
| --- | --- | --- | --- | --- |
| Stability promise | frozen for the platform's lifetime | "This ABI is *unstable* and will change between Go versions"; a separate stable `ABI0` exists for assembly, bridged by generated wrappers | stable only for "externally visible public interfaces and symbols"; internal conventions may change | not examined |
| Specification form | prose + examples | one algorithm in the compiler's repository, with rationale | prose documents (the calling-convention whitepaper is introduced as "potentially-out-of-date") + compiler | executable Python definitions "with a small unit test suite" |
| Argument placement | memory image mapped onto registers | "Each base value is assigned to its own register"; on amd64 nine integer registers `RAX, RBX, RCX, RDI, RSI, R8, R9, R10, R11` and `X0`–`X14`; "There are no callee-save registers" | platform C registers plus a *call context* register and an *error* register (x86-64: `r13` self, `r12` error, `r14` async context; arm64: `x20`, `x21`, `x22`); up to four integer return registers | flattened core-Wasm values or linear memory |
| Layout evolution | client code bakes in offsets ("a client's use of a C struct is 'fragile'") | not a cross-version interface | *resilient*: size, alignment, and field offsets of opaque-layout types are obtained at run time from value witness tables and type metadata; `@frozen` opts out, and even then "is *not* guaranteed to use the same layout as a C struct" | interface types, not layouts, are the contract |
| Strings | pointer to NUL-terminated bytes, encoding by convention | pointer plus `int` length | not examined | "two pointer-sized values: a pointer … and a number of code units", with the encoding (`utf8`, `utf16`, `latin1+utf16`) declared per function |

Go's release notes attribute "performance improvements of about 5%, and a typical reduction in
binary size of about 2%" to the register-based convention (1.17, 64-bit x86 first) — measured
against Go's previous stack-based convention, not against the C psABI. Go's rationale for
all-or-nothing placement transfers to any ABI: "Arguments that can't be fully assigned to
registers are passed entirely on the stack in case the callee takes the address of that argument."

Basis: documentation (Go `src/cmd/compile/abi-internal.md` and release notes; Swift
`docs/ABIStabilityManifesto.md`, `docs/ABI/CallingConventionSummary.rst`,
`docs/LibraryEvolution.rst`; Component Model `design/mvp/CanonicalABI.md`) + derived (the
comparison table). None of these systems was executed.

### 4. Data-representation fossils

#### 4.1 Strings without length, arrays that turn into pointers

Ritchie records both decisions as local, pragmatic, and early. On strings: "In BCPL, the first
packed byte contains the number of characters in the string; in B, there is no count and strings
are terminated by a special character … This change was made partially to avoid the limitation on
the length of a string caused by holding the count in an 8- or 9-bit slot, and partly because
maintaining the count seemed, in our experience, less convenient than using a terminator." On
arrays: B arrays were pointer cells; when structures arrived, a struct containing an array (his
example is the directory entry `struct { int inumber; char name[14]; }`) had "no good place
to stash the pointer". The fix "eliminated the materialization of the pointer in storage, and
instead caused the creation of the pointer when the array name is mentioned in an expression. The
rule, which survives in today's C, is that values of array type are converted, when they appear in
expressions, into pointers to the first of the objects making up the array" — an invention that
"enabled most existing B code to continue to work". His own verdict: "C's treatment of arrays in general
(not just strings) has unfortunate implications both for optimization and for future extensions."

The rule is still normative: an expression of array type "is converted to an expression with type
'pointer to type' that points to the initial element" (C11 6.3.2.1p3); a parameter declared as an
array "shall be adjusted to" a pointer (6.7.6.3p7); and a string is "a contiguous sequence of
characters terminated by and including the first null character" (7.1.1p1). So no psABI passes a C
array by value or carries its length; a length, if any, is a second, unrelated argument. AAPCS64
notes that its algorithm "makes provision for languages other than C and C++ in that it provides
for passing arrays by value".

Basis: documentation (Ritchie) + normative (C11; AAPCS64) + derived (the ABI consequence).

#### 4.2 Pointers that are almost integers

BCPL and B had one type, the cell; "Memory in these languages consists of a linear array of such
cells", and a pointer was an index into it. The PDP-11's byte addressing made that representation
costly ("Each pointer reference generated a run-time scale conversion"), one of three stated
reasons for adding types. Early C still "manifested strong signs of its typeless origins.
Pointers, for example, were barely distinguished from integral memory indices"; the `unsigned`
types "were added to make unsigned arithmetic available without confusing it with pointer
manipulation". The surviving normative rule keeps the door open: "An integer may be converted to
any pointer type" and "Any pointer type may be converted to an integer type", both with
implementation-defined results (C11 6.3.2.3p5–6). All three psABIs classify pointers as plain
integers, so no provenance, bounds, or ownership crosses a call.

Basis: documentation (Ritchie) + normative (C11; psABI classification of pointers as INTEGER).

#### 4.3 Integer promotions and conversions

The rules (C11 6.3.1.1p2, 6.3.1.8p1; unchanged in substance in N3220): any type of rank below
`int` is converted to `int` if `int` can represent all its values, otherwise `unsigned int`;
binary operators then convert both operands to a common type chosen by rank and by whether the
signed type can represent every value of the unsigned one. Signed overflow is undefined (6.5p5);
out-of-range conversion to a signed type is implementation-defined (6.3.1.3p3). C23 fixes the
representation ("The sign representation defined in this document is called two's complement.
Previous editions … additionally allowed other sign representations") but keeps the overflow rule.

Because the outcome depends on type *widths* and on `char` signedness, both of which are psABI
choices, the same expression has different values on different platforms:

| Expression | LP64, signed `char` (System V AMD64) | LLP64, signed `char` (Microsoft x64) | LP64, unsigned `char` (AAPCS64) |
| --- | --- | --- | --- |
| `~(unsigned char)0xFF` | −256 | −256 | −256 |
| `-1 < 1u` | 0 | 0 | 0 |
| `-1L < 1u` | **1** | **0** | **1** |
| `((unsigned short)1 - (unsigned short)2) < 0` | 1 | 1 | 1 |
| `(1u - 2u) < 0` | 0 | 0 | 0 |
| `(char)0xFF == 0xFF` | **0** | **0** | **1** |
| `(unsigned short)0xFFFF * (unsigned short)0xFFFF` | undefined | undefined | undefined |
| `0xFFFFu * 0xFFFFu` | 4294836225 | 4294836225 | 4294836225 |

The seventh row is the classic sign-flip hazard: two *unsigned* 16-bit operands are promoted to
*signed* `int`, and their product 4 294 836 225 exceeds `INT_MAX`. The same promotions apply at
call boundaries as the *default argument promotions* ("the integer promotions are performed on
each argument, and arguments that have type float are promoted to double", C11 6.5.2.2p6), which is
why `va_arg(ap, char)` or `va_arg(ap, float)` can never be correct (7.16.1.1p2 makes a type
mismatch with the promoted argument undefined).

Basis: normative (C11/N3220 clauses cited; psABI and AAPCS64 type tables for widths and `char`
signedness; Microsoft scalar-type table) + derived (table computed by the probe's model of
6.3.1.1/6.3.1.8) + execution (the twelve defined expressions in the probe's list, a superset
of this table, evaluated by GCC 15.2.0 on LP64; the unsigned-`char` row checked with `-funsigned-char`; the 32-bit-`long` result of `-1L < 1u`
checked with `-m32`, which shares the relevant ranks with LLP64).

#### 4.4 Declaration-order layout, bit-fields, unions

C fixes only the order: "the non-bit-field members and the units in which bit-fields reside have
addresses that increase in the order in which they are declared … There may be unnamed padding
within a structure object, but not at its beginning" (C11 6.7.2.1p15). Bit-field allocation is
explicitly delegated: whether a field straddles units "is implementation-defined. The order of
allocation of bit-fields within a unit … is implementation-defined. The alignment of the
addressable storage unit is unspecified" (6.7.2.1p11). A union stores "at most one of the members"
with no discriminant (6.7.2.1p16). Ritchie's motive for the layout rule was overlaying external
data: "I wanted the structure not merely to characterize an abstract object but also to describe a
collection of bits that might be read from a directory."

The psABIs supply the missing rules ("Each member is assigned to the lowest available offset
with the appropriate alignment"), and for bit-fields *different* rules (finding 2). Layout is
thus part of every C interface and every field change an ABI change — the property Swift's
resilience model removes (finding 3).

Basis: normative (C11; psABI "Aggregates and Unions", "Bit-Fields"; Microsoft documentation) +
documentation (Ritchie) + execution (sizes and alignments of 16 specimen types and 4 bit-field
specimens match the model under GCC 15.2.0).

#### 4.5 A deallocator that forgets size, and aliasing facts that do not cross

`void free(void *ptr)` receives only the pointer; passing anything not "earlier returned by a
memory management function" is undefined (C11 7.22.3.3p2). C23 adds
`free_sized(void *ptr, size_t size)` (N3220 7.24.3.4: equivalent to `free` when `size` equals the
requested size, otherwise undefined; "A conforming implementation may ignore size") and
`free_aligned_sized` (7.24.3.5). The retrofit shows the omission was contingent; the Canonical
ABI's `realloc(old, old_byte_length, alignment, new_byte_length)` shows an interface designed with
the information present.

C's aliasing contracts — an object's stored value may be accessed only through an lvalue of a
compatible, character, or related type (C11 6.5p7), and `restrict` (6.7.3p8, 6.7.3.1) — are
properties of C translation units. Nothing in the three psABIs encodes them. The only aliasing
statement in the psABI calling sequence concerns the hidden result buffer: "This storage must not
overlap any data visible to the callee through other names than this argument." Any other
exclusivity or immutability guarantee is absent from the machine-level contract and must be
re-established by convention or proof on the far side.

Basis: normative (C11, N3220, psABI "Returning of Values") + documentation (Canonical ABI) +
derived (absence claim: the calling-sequence chapters of the three psABI texts were searched for
aliasing, ownership, and lifetime rules and only the quoted sentence was found).

### 5. Stack and control-flow conventions

#### 5.1 The native stack contract

All three conventions assume one contiguous, downward-growing region per thread, addressed by a
dedicated register, 16-byte aligned at calls. They differ below and above the stack pointer
(finding 1): System V grants 128 bytes below `rsp` that "shall not be modified by signal or
interrupt handlers"; Microsoft grants nothing below `rsp` but obliges every caller to reserve 32
bytes of home space, and requires a call to `__chkstk` before any fixed allocation of a page
(4096 bytes) or more "to ensure that the stack is extended properly"; AAPCS64 models the stack as
`[limit, SP)` inactive and `[SP, base)` active, forbids all access to the inactive part, and
describes a chain of frame records through the frame pointer `x29`, leaving the required level
of maintenance to each platform. Probe intervals, guard pages, and actual red-zone use are
covered for rustc in `rust-stack-discipline-probes-red-zones-and-overflow`.

Basis: normative (psABI "The Stack Frame"; Microsoft "x64 stack usage", "x64 prolog and epilog";
AAPCS64 "The Stack", "The Frame Pointer").

#### 5.2 Why native frames pin runtimes

A precompiled C function (a) may use an unknown amount of stack, (b) may store raw addresses of
its own frame anywhere, with no map a runtime could use to find and rewrite them, and (c) assumes
its return address and callee-saved registers stay where the psABI put them. A language runtime
that wants cheap tasks must respond to that, and each known response is visible in a primary
source:

- **Movable stacks plus a stack switch at the boundary (Go).** Goroutine stacks start at
  `stackMin = 2048` bytes and grow by `copystack`, which allocates twice the size
  (`newsize := oldsize * 2`), copies the frames, and rewrites interior pointers from per-frame
  pointer maps — sound only for frames the Go compiler produced: "We can't copy the stack
  if we're in a syscall. The syscall might have pointers into the stack and often we don't have
  precise pointer maps for the innermost frames." Hence a cgo call "switches to the m->g0 stack
  (assumed to be an operating system-allocated stack, so safe to run gcc-compiled code on)", and
  "g0 stacks never move". Go 1.3 had already replaced segmented stacks with this contiguous model
  to eliminate "the old 'hot spot' problem when a calculation repeatedly steps across a segment
  boundary".
- **Pinning (Java).** A virtual thread "cannot be unmounted during blocking operations because it
  is pinned to its carrier … when it executes a native method or a foreign function"; the JEP
  states that this limitation "is required for proper interaction with native code".
- **One native stack per task, or no stack at all (Rust).** RFC 230 removed green threads:
  "segmented stacks come with a significant performance and complexity cost", and tasks without
  their own stack "either cannot be migrated between underlying worker threads … or else must be
  implemented using continuation-passing style (CPS) … (CPS essentially moves the needed parts of
  the stack into the continuation closure.)" The second branch is the stackless-coroutine design
  whose user-visible cost — a function is either suspendable or not — Nystrom's essay "What Color
  is Your Function?" (2015-02-01) named; the same essay identifies the escape hatch as "multiple
  independent callstacks that can be switched between".

The stackful/stackless ("coloured") split is thus a choice among ways of coexisting with
properties (a)–(c), none of them free.

Basis: source (Go `runtime/stack.go`, `runtime/cgocall.go`) + documentation (Go 1.3 release notes;
JEP 444; Rust RFC 230; Nystrom) + derived (the three-property synthesis and the mapping of
systems onto it).

#### 5.3 Out-of-band errors, non-local exits, and variadics

**`errno`.** The standard's error channel is a macro that "expands to a modifiable lvalue that has
type int and thread storage duration" and "need not be the identifier of an object" — expansion to
`(*errno())` "is a viable implementation strategy" (N3220 7.5 and footnote; C11 7.5p2 has the same
definition). It appears in no function signature and in no psABI; Swift's error register and Go's
multiple register results are the counterexamples (finding 3).

**`setjmp`/`longjmp`.** `longjmp` is undefined if "the function containing the invocation of the
setjmp macro has terminated execution" (C11 7.13.2.1p2); it runs no cleanup. The Itanium C++ ABI
therefore specifies `longjmp_unwind` as a *forced unwind* through `_Unwind_ForcedUnwind`, during
which "A runtime is not allowed to catch an exception".

**Table-driven unwinding.** The Itanium design runs a *search* pass that calls each frame's
personality routine without changing state, then a *cleanup* pass that unwinds to the chosen
handler. The document itself marks the two-pass structure as a design choice: "A two-phase
exception-handling model is not strictly necessary to implement C++ language semantics, but it
does provide some benefits", chiefly that other languages could resume. Foreign exceptions may be caught by `catch(...)`; accessing the object is
undefined. For Rust's use of this machinery see
`rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking`.

**Variadics.** The callee does not know the argument types, so the convention must let it find
"the next argument" given only a type. System V does it with a state machine over a 176-byte
register save area (`rdi`…`r9` at offsets 0–40, `xmm0`…`xmm7` at 48–160):

```c
typedef struct {
    unsigned int gp_offset;      /* next integer register slot; 48 when exhausted  */
    unsigned int fp_offset;      /* next vector register slot; 176 when exhausted  */
    void *overflow_arg_area;     /* next stack argument                            */
    void *reg_save_area;
} va_list[1];
/* va_arg(l, T): if T is register-class, gp_offset <= 48 - 8*num_gp and fp_offset <= 176 - 16*num_fp:
                 fetch from reg_save_area and advance both offsets;
                 else align overflow_arg_area to 16 if alignof(T) > 8, fetch, advance, round up to 8. */
```

Transitions observed with GCC 15.2.0 for `f(int n, ...)` fetching `int`, `double`, `long long`,
`long double`, `struct { double; long long; }`, `__int128`, `int`, then seven `double`
(`gp_offset, fp_offset, overflow bytes`):

```text
start (8,48,0) → (16,48,0) → (16,64,0) → (24,64,0) → (24,64,16) → (32,80,16) → (48,80,16)
→ (48,80,24) → (48,96,24) → … → (48,176,24) → (48,176,32)
```

`long double` always comes from the overflow area (class X87 is memory-passed); the mixed
INTEGER+SSE struct takes one slot of each kind or, if either is exhausted, none (with six named
integers: `(48,48,0) → (48,48,16)`). AAPCS64 uses the mirror-image design
— `__gr_offs` and `__vr_offs` start at `−8·(8 − named_gr)` and `−16·(8 − named_vr)` and count up
to zero, with rounding to 16 for 16-byte-aligned types — while Microsoft x64 and Apple arm64 avoid the
state machine by giving every variadic argument a stack slot: Microsoft's home space makes the
four register arguments contiguous with the stack arguments (GCC's `ms_abi` `va_list` was observed
to be a pointer advancing 8 bytes per argument), and LLVM's Apple variadic convention is
"Everything is on the stack". C23 removes one historical source of such calls: a declarator without a parameter list now means
`(void)` (N3220 6.7.7.4p13), and `va_start` no longer needs a named last parameter.

Basis: normative (C11, N3220, psABI "Variable Argument Lists", AAPCS64 appendix "Variable argument
lists", Itanium C++ ABI exception handling level I) + execution (System V transitions; the `ms_abi`
pointer `va_list` advancing 8 bytes per argument for types of at most 8 bytes) + derived (AAPCS64
transitions, model-only).

### 6. Contingency versus irreducible constraint

"Contingent": a recorded origin exists *and* a deployed system does otherwise. "Irreducible":
what the counterexample still has to do.

| Convention | Evidence of contingency | What remains irreducible |
| --- | --- | --- |
| Calling convention defined by prose and re-implemented per tool | Eleven documented divergences (finding 2); the Canonical ABI is executable; Go's is one algorithm in one repository | Caller and callee, compiled without sight of each other, must compute the *same function* from signature to machine locations, so it must exist in a form both can run or check |
| Which registers, how many, which are preserved | Go: 9 integer argument registers, no callee-saves; Swift adds context and error registers; Microsoft: 4 positional slots — all on the same hardware | The register file is finite; overflow needs an agreed memory location; the save/restore partition must be fixed in advance for calls whose target is unknown at compile time |
| Aggregates travel as their memory image cut into 8-byte pieces | Go assigns each field its own register; AAPCS64 special-cases homogeneous FP aggregates; Microsoft passes most by reference | All-or-nothing placement: four unrelated conventions forbid splitting one argument across registers and stack, and Go states why (address-taken reconstruction) |
| NUL-terminated strings; arrays as bare pointers | BCPL had counted strings; Ritchie gives the 8/9-bit count field as a reason; Canonical ABI passes pointer, length, and declared encoding | A view of contiguous data needs an address and an extent that both sides interpret identically, and text needs an agreed encoding |
| Integer zoo and promotions | Results flip with data model and `char` signedness (finding 4.3); C23 could fix the sign representation only after decades | Machine arithmetic is fixed-width; an interface must state width, signedness, and what overflow means |
| Declaration-order layout; implementation-defined bit-fields | Two incompatible bit-field algorithms in vendor texts; Swift lays out resilient types at run time | Parties sharing memory need identical offsets, sizes, and alignments — frozen in advance or obtained through an agreed indirection; alignment itself is forced by atomic and vector instructions and affects cache-line sharing |
| `free(ptr)` without size or allocator identity | C23 `free_sized`; Canonical ABI `realloc` with old size and alignment | Transferring ownership across a boundary requires agreeing who deallocates, with which allocator, and with what information |
| Aliasing and exclusivity invisible at the boundary | Not in any psABI; exists only in source-language rules | An optimizer or verifier on either side needs separation facts; if they are not carried, they must be assumed absent |
| One contiguous native stack per thread, red zone, guard pages | Go moves and resizes its own stacks | Frames whose interior pointers cannot be enumerated cannot move, and code of unknown stack depth needs headroom: hence stack switches (Go), pinning (JVM), or stackless tasks |
| `errno` | Swift error register; Go multiple results | A failure signal that costs nothing on the success path and that a foreign caller can observe |
| Two-pass table-driven unwinding | Its own specification: "not strictly necessary to implement C++ language semantics" | On a non-local exit every intervening frame, in any language, must get to release its resources by an agreed protocol |
| Untyped variadics and `va_list` state machines | C23 deletes unprototyped declarations; interface languages with typed lists need none | None found for typed interfaces; needed only for compatibility with existing variadic C functions |
| Layout and calling details frozen forever | Swift separates a stable public interface from free internals; Go keeps `ABIInternal` unstable behind wrappers | Where separately *versioned* components meet, something stays fixed: the representation, or the protocol for asking about it |

Basis: derived (synthesis of findings 1–5). The cache-line remark is general reasoning, not
measured here.

### 7. What the probe establishes

`support/verify_c_abi_contingencies.py` (Python ≥ 3.10, standard library only) models natural
layout, two bit-field allocators, the three calling conventions with Apple's deviations, both
`va_list` state machines, and C integer conversion under three data models. It checks 80 model
results against expectations transcribed from the specifications. When an x86-64 Linux C
compiler is present it also compiles generated C and observes:

- **arguments**: each test function is called through a mismatched prototype that loads every
  integer register, vector register, and twelve stack slots with byte-unique sentinels, so each
  byte the callee copies out names its origin (16 System V signatures; 4 Microsoft signatures via
  a variadic prototype, which makes GCC load both registers of each position);
- **return values**: an assembly trampoline poisons `rax`, `rdx`, `xmm0`, `xmm1`, clears the x87
  stack, supplies a candidate result buffer, calls, and records all of them (10 + 6 cases);
- **`va_list`**, **integer expressions**, **`sizeof`/`_Alignof`**, and **bit-field layout**.

The recorded run with GCC 15.2.0 gives 80/80 model checks and 45/45 compiler checks, exit
status 0, plus two notes (D10, D11). Those totals describe the checks in their final form; two
were revised during development after a mismatch:

- the hand-derived AAPCS64 `va_list` expectation was wrong when first written (the model
  disagreed) and was re-derived from the specification's pseudo-code. Model and expectation both
  rest on one reading of the same text, so the AAPCS64 results have no independent check;
- the `ms_abi` `va_list` check first asserted 8-byte advancement for a 16-byte struct and
  `__int128` too. It failed against GCC (44/45). The model was kept, the assertion narrowed to
  types of at most 8 bytes, and the failing case is reported as D10 instead of being counted.

Four hand-picked model mutations — Microsoft 16-byte aggregates by value, INTEGER+SSE merging to
SSE, x87 `long double` as an integer pair, conversions always signed 64-bit — were each detected
by both layers. That shows these four errors would be caught, not that the checks are exhaustive.

Basis: execution (`support/probe_output.txt`, `support/probe_results.json`) + derived (the model).

## Boundaries

**Not examined.**

- MSVC and any Windows target; Microsoft-convention execution is GCC's `ms_abi`/`ms_struct`
  emulation on Linux, so D10 says nothing about GCC on Windows targets.
- Execution with Clang, rustc, libffi, Swift, or Go; any AArch64 or Apple execution. The
  AAPCS64 and Apple results are one reading of the text checked only against itself.
- Other ABIs (i386, x32, RISC-V, PowerPC, s390x, the WebAssembly C ABI); C++ parameter rules;
  complex types, `_BitInt`, `_Float16`, decimal floating point, vector aggregates, SVE/SME.
- The PDP-11 calling sequence, early Unix system-call error reporting, and the raw Linux
  system-call convention: no primary source was read, so nothing is claimed about the origin of
  `errno` beyond its normative definition.
- The ANSI C Rationale and the unsigned-preserving versus value-preserving promotion debate;
  Ritchie says only that X3J11 adopted "slightly different type promotion rules".
- Capability hardware, descriptor-based calling standards, COM/WinRT, and other counterexamples
  beyond Go, Swift, and the Component Model; the performance of any alternative; unwind table
  encodings.

**Unknown.**

- Whether psABI commit `e1ce0983…` (2025-03-12) is still the head of its repository: files and
  commit feed came through an intermediary fetch service, so identity is pinned but recency is
  not established.
- Whether D10 is reported upstream and which GCC versions it affects; whether D11 is regarded
  upstream as a documentation error or a compiler deviation.
- Whether the published ISO/IEC 9899:2011 and 9899:2024 texts differ from N1570 and N3220 in any
  cited clause.
- Whether GCC honours the unspecified-excess-bits rule on every code path (Clang's documentation
  says GCC follows the platform ABI; GCC source was not read for this).

**Known not to apply.** The System V red zone does not exist under the Microsoft convention or
base AAPCS64; the AAPCS64 even-register rule and 8-byte minimum stack slot do not apply on Apple
platforms; eightbyte classification plays no role in the positional, size-based Microsoft
convention.

**Unsupported.** libffi rejects vector shapes outside those GCC and Clang agree on
(`FFI_BAD_TYPEDEF`). The probe's compiler layer runs only on x86-64 Linux; elsewhere it reports
"skipped" and only the model layer is evaluated.

**Stronger conclusions the evidence does not support.**

- That today's compilers disagree on common types: every divergence in finding 2 concerns an edge
  type, an old compatibility level, a non-vendor type, or an emulated ABI.
- That C interoperability *caused* the stackful/stackless split: the sources show native frames
  constrain stack management, and also cite memory footprint, I/O integration, and maintenance.
- That a replacement ABI would be simpler: the matrix lists obligations, not the cost of meeting
  them.
- That the model implements any psABI completely: it covers the types under Applicability and the
  cases enumerated in the probe.

## Evidence

All material was acquired on 2026-11-19; line numbers are at the pinned revisions.

**Specifications.**

- x86-64 psABI, `gitlab.com/x86-psABIs/x86-64-ABI` @ `e1ce098331da5dbd66e1ffc74162380bcc213236`,
  `x86-64-ABI/low-level-sys-info.tex`: scalar-type figure 129–260; aggregates and bit-fields
  316–403 (plain bit-field sentence 384); stack frame and red zone 482–541; classification and
  passing 571–805 (excess bits 716–723, reversion rule 779–782, `al` 792–800); returning of values
  806–835 (non-overlap sentence 814); worked example 837–900; variable argument lists 2237–2440
  (save-area figure 2325–2345, `va_list` 2349–2376, thresholds 2389–2397, algorithm 2400–2440).
  Commit messages for `ab2062ad5653913c39124548943b1177330e34c8` (D1) and `e1ce0983…` (D2) from
  the repository's `master` commit feed.
- AAPCS64, `ARM-software/abi-aa` @ `9f9e067e6c6a5d3c5c8326756500cdbd940b8ff7`,
  `aapcs64/aapcs64.rst`: homogeneous aggregates 756–771; stack constraints 1186–1224; parameter
  passing stages A–C 1911–2100; result return 2101–2118; C type mapping 2790–2860 (`char` 2792,
  `long double` 2828); variable argument lists 3435–3560 (review note 3556).
- Microsoft, `MicrosoftDocs/cpp-docs` @ `807f0a38b59bddf9c727b7786e36e79cb5e8d00f`:
  `docs/build/x64-calling-convention.md` (lines 16–24, 38–58, examples 60–88, varargs 89–102,
  returns 104–108); `docs/build/stack-usage.md` line 8; `docs/build/prolog-and-epilog.md` lines
  10, 30–44; `docs/build/x64-software-conventions.md` (scalar table 45–58, bit-fields 172–174);
  `docs/c-language/storage-and-alignment-of-structures.md` line 18;
  `docs/c-language/c-bit-fields.md` lines 45–49; `docs/cpp/fundamental-types-cpp.md` line 56.
- C: WG14 N1570 (2011-04-12) clauses 6.2.5, 6.2.6.2, 6.3.1.1, 6.3.1.3, 6.3.1.8, 6.3.2.1, 6.3.2.3,
  6.5, 6.5.2.2, 6.7.2.1, 6.7.3, 6.7.6.3, 7.1.1, 7.5, 7.13.2.1, 7.16.1.1, 7.22.3.3; WG14 N3220
  clauses 6.2.6.2, 6.5.1, 6.7.7.4, 7.5, 7.16.1, 7.24.3.4, 7.24.3.5. Both were read in a
  third-party HTML rendering of the WG14 documents (`https://port70.net/~nsz/c/c11/n1570.html`,
  `https://port70.net/~nsz/c/c23/n3220.html`), not in the WG14 PDFs themselves.
- Itanium C++ ABI, `itanium-cxx-abi/cxx-abi` @ `fae5e46c86147a457a057c6372fa95ec38209fe8`,
  `abi-eh.html`, level I sections on the two-pass process, forced unwinding, and foreign
  exceptions.

**Implementations (source).**

- `llvm/llvm-project` @ `ffcd0a522aedc16a966e3efb9a97a336be8ddb57`:
  `clang/lib/CodeGen/Targets/X86.cpp` — `getEffectiveSmallIntABICompat` 474–480, compatibility
  predicates 1443–1485, `postMerge` 1923–1954, `merge` 1982–2020, `classify` 2022–2411
  (`__int128` 2042, `<1 x double>` 2123, union rule 2324–2331), `classifyArgumentType` 2966–3075
  (small-integer switch 3026–3040), `EmitVAArg` 3348–3560 (304 note 3378–3383, 176 at 3399),
  `WinX86_64ABIInfo::classify` 3601–3767 (`__int128`/`__float128` 3712–3747);
  `clang/lib/CodeGen/Targets/AArch64.cpp` — empty records 442–461, small aggregates 498–548, member limit 708–711; `clang/include/clang/Options/Options.td` 5819–5862;
  `clang/include/clang/Basic/CodeGenOptions.h` 286–290;
  `llvm/lib/Target/AArch64/AArch64CallingConvention.td` 378–381, 459–476.
- `rust-lang/rust` @ `b0b600668bb9b4a897e2299b0a44289d42276545`,
  `compiler/rustc_target/src/callconv/`: `x86_64.rs` 1–2, 34–40, 301–314; `x86_win64.rs` 30–37,
  47–50; `aarch64.rs` 8–17, 141–149.
- `libffi/libffi` @ `de7afe7aa9e8ab7ac36429428a7222caae1e7988`: `src/x86/ffi64.c` 77–78,
  445–456; `src/aarch64/ffi.c` 283–292, 549–574, 897–903.
- `gcc-mirror/gcc` @ `5115c7e447fc07457443df874bf57840e8316d5f` (tag `releases/gcc-15.2.0`):
  `gcc/config/i386/i386.cc` `ix86_pass_by_reference` 3545–3580 and `ix86_gimplify_va_arg`
  4858–4859; `gcc/calls.cc` `pass_va_arg_by_reference` 964–968; `gcc/targhooks.cc` 2574.
- `golang/go` @ `b496a3044e1dcdc3eed0af3e0e89db92f740d764`: `src/cmd/compile/abi-internal.md`
  lines 1–25, 119–170, 221, 257–300, 384–400 (the specification's path is `abi-internal.md`);
  `src/runtime/cgocall.go` 5–83; `src/runtime/stack.go` 78, 954–1030, 1204, 1265–1280.

**Documentation and history.**

- Ritchie, "The Development of the C Language", ACM SIGPLAN Notices 28(3), March 1993,
  pp. 201–208, DOI `10.1145/155360.155580` (record confirmed through Crossref); quotations from
  the author's electronic reprint.
- `swiftlang/swift` @ `466f30162134b2c16b0f05c05d766cdd151236a5`:
  `docs/ABIStabilityManifesto.md` 29–33, 103–109, 247–253, 307–334;
  `docs/ABI/CallingConventionSummary.rst` (x86-64 and arm64 register tables);
  `docs/LibraryEvolution.rst` 11–26, 121–126, 487–489.
- `WebAssembly/component-model` @ `585526aa1f2c7f76f07557d16e265dede38b3acb`,
  `design/mvp/CanonicalABI.md` 11–24, 982–1009, 2198–2260.
- `golang/website` @ `0eef789c9f9a7cc074eab1b3fb2d96baea282546`: `_content/doc/go1.3.md` 86–94;
  `_content/doc/go1.17.md` 373–392.
- `rust-lang/blog.rust-lang.org` @ `5b42e9f522217dd60b9f2258b10c98f6601b7cc2`,
  `content/i128-layout-update.md` (post dated 2024-03-30).
- `rust-lang/rfcs` @ `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `text/0230-remove-runtime.md`
  44–62, 78–92.
- JEP 444 "Virtual Threads", `https://openjdk.org/jeps/444` (updated 2025/10/30), pinning
  section. Nystrom, `https://journal.stuffwithstuff.com/2015/02/01/what-color-is-your-function/`.

**Execution.** Host: x86-64 Linux; `cc` = `gcc (Debian 15.2.0-14) 15.2.0`; Python 3.13.15.
Command, run from the package's `support/` directory:

```console
python3 -B verify_c_abi_contingencies.py --json probe_results.json > probe_output.txt
```

Exit status 0. `support/probe_output.txt` is the full transcript of the last run;
`support/probe_results.json` holds the same content as JSON. Earlier development runs (one
model-only run at 79/80, one full run at 44/45; see finding 7) are not preserved. Generated C
sources are regenerated deterministically (`--keep` leaves them in a temporary directory). The
four-mutation run replaced `win64_mode`, `_merge`, the System V `long double` entry, and `usual`
in turn through a module import; it is not in the transcript.

## Revalidation

1. **Cheapest check.** Run `python3 -B support/verify_c_abi_contingencies.py`. Any host re-derives
   the 80 model results; x86-64 Linux with a C compiler also repeats the 45 run-time
   observations, and `--cc clang` (or another driver) repeats them for a different compiler. A
   pass establishes agreement only for the enumerated types and signatures.
2. **Watch the two `NOTE` lines** of the transcript: D10 (`ms_abi` `va_arg` of a 16-byte struct)
   and D11 (plain bit-field signedness). A change there means the compiler changed, not the model.
3. **When a specification moves**, diff only the rule-bearing regions: psABI
   `low-level-sys-info.tex` paragraphs "Classification", "Passing", "Returning of Values" and
   section "Variable Argument Lists"; AAPCS64 stages B and C and the `va_arg` appendix (is the
   review note gone?); Microsoft `x64-calling-convention.md`. Then update `sysv_classify`,
   `win64_args`, or `a64_args` in the probe and its expectations.
4. **When an implementation moves**, re-read the regions listed under Evidence, starting with
   Clang's `-msmall-int-abi-compat` default and GCC's `ix86_pass_by_reference`.
5. **AArch64 has no cheap check here.** Confirming that column needs an AArch64 compiler and the
   same sentinel technique over `x0`–`x7`, `v0`–`v7`, and `x8`. For the counterexample systems,
   re-read the quoted passages at the paths under Evidence.
