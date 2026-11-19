# COBOL Packed Decimal & REDEFINES, MUMPS Globals, Fortran Aliasing & CFI Descriptors, and MATLAB MEX Boundaries

## Summary

Legacy financial, healthcare, and scientific computing ecosystems embed data-layout, aliasing, and control-flow invariants that diverge sharply from C and Rust memory models and silently break naive FFI wrappers or compiler-based verification passes:

1. **COBOL (`ISO/IEC 1989:2023`, GnuCOBOL 4)**:
   - `COMP-3` (`USAGE PACKED-DECIMAL`) stores two base-10 digits per byte plus a low-order 4-bit sign nibble (`0xC` positive, `0xD` negative, `0xF` unsigned; width $\lfloor d/2 \rfloor + 1$ bytes) and performs **silent left-truncation on overflow** unless `ON SIZE ERROR` is present.
   - `REDEFINES` overlays arbitrary numeric, packed-decimal, and alphanumeric (`PIC X`) views onto identical raw storage with **no discriminant tag**; reading non-BCD bytes (such as ASCII/EBCDIC spaces or text) through a `COMP-3` alias triggers hardware `S0C7` Data Exceptions on IBM z/Architecture or invalid-nibble decoding unless guarded by `IS NUMERIC`.
   - `PERFORM A THRU B` creates **irreducible control-flow graphs**: paragraphs are entry points without lexical scope or fixed return blocks. GnuCOBOL lowers `PERFORM THRU` to an explicit runtime stack (`frame_ptr++`, `frame_ptr->perform_through = le->id`, `goto l_<lb>`) with dynamic computed-`goto` epilogue checks; jumping out of an active range via `GO TO` or overlapping ranges corrupts or leaks active return frames.
2. **MUMPS / M (`ANSI/MDC X11.1-1995`, YottaDB)**:
   - Variables prefixed with `^` (`^GLOBAL(s1, s2, ...)`) address a **persistent, sparse, hierarchical B-tree** directly integrated into language assignment and iteration (`$ORDER`/`$QUERY`).
   - Subscripts obey **canonical-numeric-before-string collation** (`"" < -10 < -2 < -.5 < 0 < .5 < 2 < 10 < "+2" < "0.5" < "01" < "1.0" < "1a"`): leading/trailing zeroes (`"0.5"`, `"01"`, `"1.0"`) are **non-canonical** strings and sort *after* all canonical numbers. YottaDB (`mval2subsc.c`) encodes exponents and inverted negative base-100 digit tables directly into B-tree keys so raw byte comparison enforces ANSI collation.
   - `@` indirection (`op_indname.c`) and `XECUTE` dynamically parse variable names, subscripts, arguments, and code from strings at runtime, preventing closed-world static alias or call-graph analysis, while `TSTART`/`TCOMMIT` execute under optimistic concurrency control (`t_end.c`, `cdb_sc_*` restarts).
3. **Fortran (`ISO/IEC 1539-1:2023`, LLVM Flang, GCC GFortran)**:
   - ISO Fortran §15.5.2.13 forbids aliasing between a modified dummy argument and any other dummy argument or accessible global/module/COMMON entity (absent `TARGET`/`POINTER` or `ASYNCHRONOUS` exemptions). Both **GFortran** (`TYPE_QUAL_RESTRICT` in `trans-types.cc`) and **LLVM Flang** (`fir::AliasAnalysis` `SourceKind::Argument` in `AliasAnalysis.cpp`) lower this rule into aggressive compiler `noalias`/`restrict` proofs. Calling Fortran kernels from C or Rust with overlapping buffers causes **silent miscompilation** (verified on GCC 15.2.0 `-O2`).
   - `COMMON` and `EQUIVALENCE` establish untagged byte-offset storage association (`trans-common.cc` lowers them to GCC `UNION_TYPE` fields with explicit byte offsets and `DECL_PACKED`), while non-contiguous array slices passed to explicit-shape dummies trigger hidden **copy-in/copy-out temporaries** that invalidate cached C pointers.
   - **`ISO_Fortran_binding.h` (`CFI_cdesc_t`) is source-compatible but NOT binary-ABI-compatible across Fortran compilers**: direct comparison of pinned headers establishes that LLVM Flang (`CFI_VERSION = 20240719`, `rank`, `type` (`signed char`), `attribute` (`other=0, pointer=1, allocatable=2`), `extra`) and GCC GFortran (`CFI_VERSION = 1`, `rank`, `attribute` (`pointer=0, allocatable=1, other=2`), `type` (`int16_t`), no `extra`) disagree on field order, integer widths, and enum encodings.
4. **MATLAB MEX FFI Boundaries**:
   - MATLAB arrays are **1-based and column-major** (matching Fortran, transposing C/Rust row-major layouts).
   - MATLAB workspace variables share heap buffers via **Copy-on-Write (CoW)**. In the C Matrix API (`mex.h`), `const mxArray *prhs[]` inputs are strictly read-only; mutating `prhs[i]` in-place silently corrupts aliased caller variables unless explicitly cloned via `mxDuplicateArray` (or accessed via the C++ MATLAB Data API's CoW-aware `TypedArray`).
   - Starting in **R2018a** (`mex -R2018a`), MATLAB transitioned from separated real/imaginary arrays (`mxGetPr`/`mxGetPi`) to **interleaved complex storage** (`mxGetComplexDoubles`), and error exits via `mexErrMsgIdAndTxt` unwind control directly back to MATLAB (bypassing C++ destructors / Rust `Drop` unless caught, while reclaiming MEX-managed allocations unless marked persistent via `mexMakeMemoryPersistent`).

## Applicability

This report serves engineers building static analyzers, binary-layout/FFI verification contracts (such as Rust `unsafe` / `zerocopy` bindings to BLAS/LAPACK, COBOL copybooks, YottaDB, or MATLAB MEX), or cross-language compilers targeting legacy numeric, transactional, and scientific systems.

- **Subject relationships**:
  - **ISO/IEC 1989:2023** (COBOL) is examined alongside **GnuCOBOL 4** (`OCamlPro/gnucobol4` @ `780745d1bac79adea61808647f5a8e4b98bee8b0`) for concrete C-lowering behavior (`libcob/numeric.c`, `cobc/field.c`, `cobc/codegen.c`) and contrasted with IBM z/Architecture hardware packed-decimal trapping (`S0C7`).
  - **ANSI/MDC X11.1-1995** (MUMPS/M) is examined through **YottaDB** (`YottaDB/YDB` @ `7a1fee723cd0d2b4c127e9c670ccc72041ec4bb0`), an industrial open-source descendant of GT.M (`sr_port/mval2subsc.c`, `sr_port/op_indname.c`, `sr_port/t_end.c`).
  - **ISO/IEC 1539-1:2023** (Fortran 2023) is examined via a side-by-side source comparison of **LLVM Flang** (`llvm/llvm-project` @ `c85e6b928dfd2552497fe666f281f3d49c2c0f70`) and **GCC GFortran** (`gcc-mirror/gcc` @ `85ae7d8c7c16d1ad96c2e19e17f2e2aa739bd72e`) covering both alias analysis and `ISO_Fortran_binding.h` descriptor ABIs, complemented by a GCC 15.2.0 `-O2` C `restrict` aliasing execution probe.
  - **MATLAB MEX** is examined from MathWorks' C Matrix API / R2018a Interleaved Complex documentation and contrasted with Fortran/C array layout and allocator unwinding contracts.
- **Environment and verification scope**:
  - `cobc`, `gfortran`, `flang`, `yottadb`, and `matlab` binaries were not installed locally. Compiler lowering and ABI facts are derived from direct inspection of pinned upstream C/C++ sources (`Basis: source`), normative standards (`Basis: normative`), and documentation (`Basis: documentation`), paired with executable Python/C probes (`Basis: execution`) on Linux x86-64 (`gcc 15.2.0`, `python3`) verifying packed BCD layouts, MUMPS canonical collation, and `restrict` miscompilation.

## Findings

### 1. Cross-Ecosystem FFI and Memory-Model Hazard Matrix

Basis: normative + source + documentation + derived

| Language / Runtime | Primary Data Layout & Indexing | Aliasing / Overlay Semantics | Control-Flow / Runtime Unwind Hazard | Silent FFI / Verification Failure Mode |
| :--- | :--- | :--- | :--- | :--- |
| **COBOL** (`ISO/IEC 1989:2023`, GnuCOBOL 4) | Fixed-width EBCDIC/ASCII records, zoned decimal, `COMP-3` packed BCD ($\lfloor d/2 \rfloor + 1$ bytes, big-endian nibbles), 1-based `OCCURS` | `REDEFINES` untagged byte overlays; group moves perform raw byte copy/space-padding ignoring numeric subfields | `PERFORM A THRU B` irreducible CFG, overlapping ranges, `ALTER` mutable goto targets | Silent left-truncation on arithmetic overflow; non-BCD nibbles from `REDEFINES` causing `S0C7` traps or garbage math; stale `PERFORM` return frames |
| **MUMPS / M** (`ANSI X11.1-1995`, YottaDB) | Strings as universal scalar; sparse multi-key persistent B-trees (`^global`) with binary-encoded numeric-then-string keys | Dynamic scoping (`NEW` stack); `@` indirection and `XECUTE` resolve arbitrary global/local names at runtime | `TSTART`/`TCOMMIT` optimistic transaction restarts re-executing MUMPS code blocks (`$TRESTART > 0`) | Mis-ordered B-tree queries if caller assumes ASCII sort (`"01"` vs `10`, `"0.5"` vs `".5"`); non-idempotent C FFI side effects duplicated across `TCOMMIT` retries |
| **Fortran** (`ISO/IEC 1539-1:2023`, Flang, GFortran) | 1-based (arbitrary `lower_bound`) column-major arrays; strided dope vectors (`CFI_cdesc_t` with byte stride `sm`) | Compiler-assumed **no-alias** across modified dummy arguments (`noalias` / `TYPE_QUAL_RESTRICT`); `COMMON`/`EQUIVALENCE` untagged storage unions | Copy-in/copy-out temporaries for non-contiguous slices; `STOP`/runtime errors terminating process | Silent miscompilation when C/Rust passes aliased pointers to Fortran; silent ABI corruption when mixing Flang and GFortran `ISO_Fortran_binding.h`; dangling pointers to copy-in temporaries |
| **MATLAB MEX** (`R2018a+` C Matrix API) | 1-based column-major `mxArray`; separated (`mxGetPr`/`mxGetPi`) pre-R2018a vs interleaved (`-R2018a`) complex | Workspace Copy-on-Write (`CoW`) shared buffers behind `const mxArray *prhs[]` | `mexErrMsgIdAndTxt` non-local unwind (`longjmp`/SEH-like) skipping C++/Rust RAII destructors while freeing non-persistent `mxMalloc` blocks | In-place write to `prhs[i]` silently mutates unrelated workspace variables; ABI mismatch between `-R2017b` and `-R2018a` complex pointers; leaked non-MEX resources on `mexErrMsgIdAndTxt` |

---

### 2. COBOL: Packed Decimal (`COMP-3`), `REDEFINES` Overlays, and `PERFORM THRU` Irreducible CFGs

#### 2.1 `COMP-3` (`USAGE PACKED-DECIMAL`) Representation and Arithmetic Semantics

Basis: normative (`ISO/IEC 1989:2023`) + source (`OCamlPro/gnucobol4` @ `780745d1...`, `libcob/numeric.c` L970–974, L1144–1265; `cobc/field.c` L973–975) + execution (Probe A)

A COBOL `PIC [S]9(m)V9(n) USAGE COMP-3` (with total digits $d = m + n$) packs two decimal digits (`0..9`) per byte from most-significant to least-significant nibble, terminating with a 4-bit sign nibble in the lowest-order nibble of the final byte:

- **Byte width**: $W = \lfloor d / 2 \rfloor + 1$ bytes (when $d$ is even, the high nibble of byte 0 is a leading zero padding nibble `0x0`). ISO/IEC 1989:2023 also introduced `NO SIGN` unsigned packed-decimal (`COMP-6` in GnuCOBOL, `COB_FIELD_NO_SIGN_NIBBLE(f)` in `libcob/numeric.c` L1147), omitting the trailing sign nibble for width $\lceil d / 2 \rceil$.
- **Canonical sign nibbles**:
  - `0xC` (`1100`): preferred positive signed (`S9...`);
  - `0xD` (`1101`): preferred negative signed (`S9...`);
  - `0xF` (`1111`): unsigned (`9...`);
  - Legacy/alternate accepted signs on IBM z/OS: `0xA`, `0xE` (positive), `0xB` (negative). Note that GnuCOBOL's fast sign check (`libcob/numeric.c` L970–971) tests `((p & 0x0F) == 0x0D) ? -1 : 1` (treating `0x0D` as negative and non-`0x0D` as positive in non-strict paths, whereas strict IBM validation treats `0x0B` as negative and traps `0x0..0x9` as invalid).
- **Fixed-point scale `V` and `P`**: The decimal point `V` is purely compile-time metadata (`COB_FIELD_SCALE(f)`, `libcob/numeric.c` L1151–1158); negative scales arise from `P` scaling positions (`99P` has 3 logical digits, scale `-1`, storing only 2 packed digits). GnuCOBOL converts `COMP-3` operands into arbitrary-precision GMP `mpz_t` (`cob_decimal`, `libcob/numeric.c` L1254–1264) for exact decimal arithmetic before converting back.
- **Silent left-truncation on overflow**: Unless the statement includes an `ON SIZE ERROR` clause, COBOL arithmetic and `MOVE` statements **silently discard high-order digits** that exceed the target `PIC` width. As verified in Probe A, storing `123456` into `PIC S9(5) COMP-3` writes `23 45 6c` (`23456`), never wrapping modulo $2^k$ like binary integers and never raising an error by default.

#### 2.2 `REDEFINES` Untagged Storage Overlays and Invalid-BCD Traps

Basis: normative (`ISO/IEC 1989:2023`) + source (`OCamlPro/gnucobol4` @ `780745d1...`, `cobc/field.c` L616–631) + execution (Probe A)

COBOL's `REDEFINES` clause (`cb_resolve_redefines`, `cobc/field.c` L616) binds a new data description to the **exact same starting byte offset** as a preceding sibling field at the same level number, without any runtime tag, alignment padding guarantee beyond compiler defaults, or type-state transition check (like a C `union` without active-member provenance, plus COBOL group-level `MOVE`s treating the entire aggregate as raw `PIC X(N)` bytes):

```cobol
01 RECORD-BUF.
   05 RAW-BYTES   PIC X(3).
   05 AMT-PACKED  REDEFINES RAW-BYTES PIC S9(5) COMP-3.
```

**Validity hazard (Probe A)**:
- Writing `"123"` (ASCII `31 32 33`) or EBCDIC `"123"` (`f1 f2 f3`) or spaces (ASCII `20 20 20` / EBCDIC `40 40 40`) to `RAW-BYTES` and reading `AMT-PACKED` yields **invalid BCD bit patterns**:
  - ASCII `"123"` (`31 32 33`) has sign nibble `0x3` (invalid: not in `0xA..0xF`);
  - EBCDIC `"123"` (`f1 f2 f3`) has digit nibbles `0xF` (invalid: `> 9`);
  - Spaces (`20 20 20` / `40 40 40`) have sign nibble `0x0` (invalid).
- On IBM z/Architecture hardware (`AP`, `SP`, `MP`, `DP`, `CP`, `ZAP` instructions), executing packed arithmetic on invalid nibbles raises an immediate **Program Interruption Code `0007` (`S0C7` Data Exception)** abend. In GnuCOBOL without strict checking, arithmetic may silently decode corrupted nibbles unless the program explicitly guards access with `IF AMT-PACKED IS NUMERIC`.
- **FFI / binary-layout implication**: Any Rust `zerocopy` / `FromBytes` / `TryFromBytes` binding to a COBOL copybook containing `COMP-3` fields **cannot** treat the packed field as unconditionally valid (`FromBytes` is unsound for a numeric invariant type); it must validate every digit nibble $\in [0, 9]$ and sign nibble $\in \{\text{0xC}, \text{0xD}, \text{0xF}\}$ (or dialect-accepted $\{\text{0xA}..\text{0xF}\}$) at the `TryFromBytes` boundary!

#### 2.3 `PERFORM A THRU B` and Irreducible Control-Flow Graphs

Basis: normative (`ISO/IEC 1989:2023`) + source (`OCamlPro/gnucobol4` @ `780745d1...`, `cobc/codegen.c` L1393–1408, L7267–7359, L7561–7572)

Unlike structured procedure calls, COBOL paragraphs and sections live in a flat `PROCEDURE DIVISION` where execution naturally **falls through** from paragraph `A` into paragraph `B` unless redirected. `PERFORM A THRU B` transfers control to label `A` and installs a dynamic **exit trigger** at the end of paragraph `B`.

In GnuCOBOL (`cobc/codegen.c` L7267–7359), `output_perform_call(struct cb_label *lb, struct cb_label *le)` lowers `PERFORM lb THRU le` directly to C stack-frame manipulation plus non-structured `goto`:
```c
frame_ptr++;
if (unlikely(frame_ptr == frame_overflow))
    cob_fatal_error (COB_FERROR_STACK);
frame_ptr->perform_through = <le->id>;
frame_ptr->return_address_ptr = &&l_<return_id>; /* or return_address_num = k */
goto l_<lb->id>;
l_<return_id>:
frame_ptr--;
```
At the epilogue of paragraph `le`, GnuCOBOL checks `if (unlikely(frame_ptr->perform_through == <le->id>))` and dispatches via computed `goto *frame_ptr->return_address_ptr` (or a `switch (frame_ptr->return_address_num)` table when `-fno-computed-goto` is used, `L1393–1408`, `L7334–7352`).

**Why this breaks standard SSA/CFG analysis and structured decompilation**:
1. **Irreducible multi-entry regions**: A paragraph `P` inside `A THRU B` can be entered via fall-through from `A`, directly via `PERFORM P`, or via `GO TO P` from outside `A..B`—forming loops and subgraphs with multiple entry headers (non-reducible CFGs).
2. **Overlapping and prematurely exited ranges**: If `A` invokes `PERFORM B THRU C` (nested) or `GO TO OUTSIDE` jumps past `B` without reaching `B`'s epilogue, `frame_ptr->perform_through == B` remains active on the stack! If execution later falls through `B` during unrelated control flow, `B`'s epilogue **unexpectedly triggers the stale return jump** back to the abandoned `PERFORM` call site (`cobc/codegen.c` L7333). (Historical IBM compilers without a perform stack stored the return address in a single static slot attached to paragraph `B`, making recursive or overlapping `PERFORM`s silently overwrite return addresses.)
3. **Dynamic control-flow mutation (`ALTER`)**: Legacy COBOL's `ALTER P1 TO PROCEED TO P2` mutates a `GO TO` paragraph's target label variable at runtime (`label_l_<id>` saved/reset across independent segments in `cobc/codegen.c` L7290–7314), creating indirect jumps whose targets are path-dependent mutable state.

---

### 3. MUMPS / M (YottaDB): Persistent Sparse B-Tree `^Globals` and `@` Indirection

#### 3.1 Sparse Hierarchical `^Globals` and Canonical-Numeric Collation

Basis: normative (`ANSI/MDC X11.1-1995`) + source (`YottaDB/YDB` @ `7a1fee723cd0d2b4c127e9c670ccc72041ec4bb0`, `sr_port/mval2subsc.c` L62–260) + execution (Probe B)

In MUMPS (M), the `^` sigil distinguishes **persistent database globals** (`^PATIENT(id, "LAB", timestamp)`) from process-local variables (`PATIENT(id)`). Both are sparse, dynamically dimensioned ordered trees mapping arbitrary tuple paths of string subscripts to string values—no schema declaration, fixed arity, or dense array allocation exists. Nodes can simultaneously hold a value *and* have descendants (`$DATA` returns `0` nonexistent, `1` value only, `10` descendants only, `11` both).

**ANSI/MDC X11.1 Subscript Collation Law**:
MUMPS does **not** sort subscripts purely lexicographically (ASCII/UTF-8), nor purely numerically. Instead, subscripts partition into three strictly ordered classes:
1. **Empty string `""`** (where permitted under standard null collation; historically sorted differently in legacy GT.M vs ANSI `STDNULLCOLL`);
2. **Canonical numbers** sorted in exact numeric order ($-\infty < \dots < -10 < -2 < -0.5 < 0 < 0.5 < 2 < 10 < \dots < +\infty$);
3. **All other strings** sorted lexicographically by byte/UTF-8 code-point value, **strictly after all canonical numbers**.

Critically, a string is a **canonical number** *only* if it has no leading `+`, no leading zeroes (except `"0"` itself; note `"0.5"` is **NOT** canonical—the canonical form is `".5"`!), and no trailing fractional zeroes (`"1.0"` is **NOT** canonical!). Verified directly in Probe B:
```text
ASCII/UTF-8 order : ['', '+2', '-.5', '-10', '-2', '.5', '0', '0.5', '01', '1.0', '10', '1a', '2', 'A']
MUMPS order       : ['', '-10', '-2', '-.5', '0', '.5', '2', '10', '+2', '0.5', '01', '1.0', '1a', 'A']
```
Notice how `".5"` sorts before `"2"` (canonical numeric), whereas `"0.5"`, `"01"`, `"1.0"`, and `"+2"` sort **after `"10"`** as ordinary strings!

**YottaDB B-tree key encoding (`sr_port/mval2subsc.c` L128–260)**:
To make raw B-tree `memcmp` byte order match ANSI MUMPS collation without invoking custom comparators on every B-tree probe, `mval2subsc()` transforms each `mval` subscript into a self-delimiting binary key:
- **`0`**: encoded as single sentinel byte `SUBSCRIPT_ZERO` (`L178`).
- **Positive canonical numbers**: biased exponent byte `exp_val` (`SUBSCRIPT_BIAS + k`, `L192–236`) followed by base-100 packed mantissa bytes mapped through `pos_code[]` (`L175`, `L193`, `L256–260`), terminating cleanly so shorter prefixes sort smaller.
- **Negative canonical numbers**: bitwise-complemented exponent byte `~(exp_val)` (`L192`, `L236`) and inverted base-100 table `neg_code[]` (`L183`) plus a `0xFF` trailer, reversing lexicographic order so `-10` (`~exp` smaller) sorts before `-2` (`~exp` larger), and all negative numbers sort below `SUBSCRIPT_ZERO`.
- **Non-canonical strings**: prefixed with `STR_SUB_PREFIX` (`L143`, greater than all numeric exponent prefixes) followed by raw string bytes with bytes `<= 0x01` escaped via `STR_SUB_ESCAPE` (`L148–150`) and terminated by `KEY_DELIMITER` (`0x00`).

#### 3.2 `@` Indirection, `XECUTE`, and Optimistic Transaction Restarts

Basis: source (`YottaDB/YDB` @ `7a1fee72...`, `sr_port/op_indname.c` L31–52; `sr_port/t_end.c` L196–217, L295–317)

- **Pervasive `@` indirection**: MUMPS supports five syntactic forms of `@expr` indirection—*name indirection* (`SET @VAR=1`), *subscript indirection* (`SET @ARR@(k)=1`), *argument indirection* (`DO @TARGET`), *pattern indirection* (`IF X?@PAT`), and *value indirection*—plus arbitrary runtime compilation via `XECUTE str`. In YottaDB (`sr_port/op_indname.c` L31–52), `op_indname` coerces both target and subscript expressions to strings (`MV_FORCE_STR`), scans past unquoted `;` comment delimiters (`L45–51`), checks `MAX_SRCLINE` (`ERR_INDRMAXLEN`), and dynamically stitches `@#(...)` source fragments for on-the-fly runtime compilation. Consequently, **no static read/write set or call graph is sound** in the presence of `@` or `XECUTE` without dynamic guards.
- **Optimistic Concurrency Control (`TSTART`/`TCOMMIT`) & FFI non-idempotency**: YottaDB implements ACID transactions across shared-memory global buffers using **optimistic concurrency control (OCC)** (`t_end()` in `sr_port/t_end.c` L196–317). A transaction reads B-tree blocks without holding the database critical-section lock (`csa->now_crit`), recording block transaction numbers (`blktn`) in search histories (`srch_hist *hist1, *hist2`) and buffering writes in `cw_set_element` (`cw_set_depth`). At commit (`t_end`), YottaDB acquires crit and validates every read block's transaction number; any concurrent modification produces a `cdb_sc_*` retry code (`L204`, `L296`), incrementing `$TRESTART` and **re-executing the entire MUMPS `TSTART`..`TCOMMIT` block from the beginning** (escalating to holding crit after `t_tries >= CDB_STAGNATE`, `L310`). Any external C/Rust FFI callout invoked inside a YottaDB transaction (`$ZCALL` / external call table) may therefore be executed **multiple times** for a single logical commit and must be strictly idempotent or deferred past `TCOMMIT`.

---

### 4. Fortran: Non-Aliasing Dummy Arguments, Storage Association, and `ISO_Fortran_binding.h` Dope Vectors

#### 4.1 Compiler-Assumed Dummy-Argument Non-Aliasing vs C/Rust FFI UB

Basis: normative (`ISO/IEC 1539-1:2023` §15.5.2.13) + source (`llvm/llvm-project` @ `c85e6b92...`, `flang/lib/Optimizer/Analysis/AliasAnalysis.cpp` L40–43, L494–496, L995–1065; `gcc-mirror/gcc` @ `85ae7d8c...`, `gcc/fortran/trans-types.cc` L1198, L1596–1598, L1809–1810, L1939–1954) + execution (Probe C)

ISO/IEC 1539-1:2023 §15.5.2.13 ("Restrictions on entities associated with dummy arguments") imposes a **far stronger aliasing ban than C**: while a procedure is executing, if *any* part of an entity associated with a dummy argument is **defined** (written) or becomes undefined, no other dummy argument, module variable, `COMMON` variable, or host-associated entity may reference or define that storage location—**even if both arguments are read-write arrays of the exact same type**—unless an explicit exception applies (principally, both entities carry `TARGET`/`POINTER` attributes under §15.5.2.13(4)(b), or `ASYNCHRONOUS`/`VOLATILE` rules apply).

Both major open-source Fortran compilers encode this rule directly into their middle-end alias analyses:

1. **GCC GFortran (`gcc/fortran/trans-types.cc` L1939–1954)**:
   When lowering dummy argument array and pointer types (`gfc_build_array_type`, `gfc_get_nodesc_array_type`, `gfc_get_array_descriptor_base`), GFortran attaches C99 **`TYPE_QUAL_RESTRICT`** directly onto both `GFC_TYPE_ARRAY_DATAPTR_TYPE(type)` (`L1941–1944`) and scalar/rank-0 dummy pointer types (`L1952–1953`) whenever `restricted` is true (i.e., the dummy lacks `TARGET` and `POINTER`).
2. **LLVM Flang (`flang/lib/Optimizer/Analysis/AliasAnalysis.cpp` L995–1065)**:
   Flang's FIR `AliasAnalysis` classifies every SSA memory reference by `SourceKind` (`Argument`, `Allocate`, `Global`, `HostAssoc`, `Direct`, `Indirect`, `Unknown`) and `isData()` vs descriptor metadata (`!isData()`):
   - Two distinct `SourceKind::Argument` data references default to `AliasResult::NoAlias` unless both carry `Attribute::Target` or `Attribute::Pointer` (`L1044–1065`);
   - Descriptor metadata (`!isData()`, e.g., bounds/strides inside a `CFI_cdesc_t`) is statically disjoint from array payload data (`isData()`);
   - Even host-associated variables (`SourceKind::HostAssoc`) only alias a dummy argument when the dummy has an explicit `TARGET` attribute per F18 §15.5.2.13(4)(b) (`L1022–1040`);
   - Legacy Cray pointers that alias non-`TARGET` variables require opting out via `-unsafe-cray-pointers` (`L40–43`).

**Empirical demonstration of C/Rust-to-Fortran FFI aliasing UB (Probe C on GCC 15.2.0 `-O2`)**:
Consider a kernel `out(i) = in(i) + in(1)` (1-based Fortran; `out[i] = in[i] + in[0]` in C) compiled with Fortran-equivalent `restrict` qualifiers on `out` and `in`, called from C/Rust with `out == in == {10, 1, 2, 3}`:
- Without `restrict` (C semantics): iteration `i=0` writes `a[0] = 20`, so `i=1,2,3` read `in[0] == 20` -> **`20 21 22 23`**.
- With `restrict` (Fortran dummy-argument semantics at `-O2`): GCC hoists `in[0] == 10` out of the loop into a register -> **`20 11 12 13`**!

**FFI contract for Rust/C callers**:
- Passing the same buffer (or overlapping slices) as both input and output to a Fortran BLAS/LAPACK or `BIND(C)` routine (e.g., `dgemm(..., A, ..., A, ..., A)` or in-place `y = A*x + y` when `x` and `y` overlap) is **undefined behavior** unless the Fortran routine explicitly documents aliasing support (`TARGET` dummies or read-only inputs). In Rust, exposing a Fortran routine via safe bindings requires `&mut [T]` exclusivity against all `&[T]` inputs—Rust's borrow checker (`&mut` vs `&`) naturally matches Fortran's dummy-argument non-aliasing rule **except** when callers drop down to raw pointers (`*mut T`, `*const T`) or pass a single `&mut` split inconsistently via `unsafe`.
- **Copy-in/copy-out hazard**: When a Fortran caller passes a non-contiguous array section (e.g., `A(1:10:2)`) to an explicit-shape or assumed-size (`A(*)`) or `CONTIGUOUS` dummy argument, the compiler allocates a stack/heap contiguous temporary, copies elements in before the call, and copies back after return. Any C routine that stashes the received pointer beyond the duration of the call (e.g., async I/O or callback registration) silently reads freed/stale stack memory unless the Fortran argument is declared `ASYNCHRONOUS` / `TARGET` + assumed-shape (`CFI_cdesc_t`).

#### 4.2 `COMMON` and `EQUIVALENCE` Untagged Storage Association

Basis: normative (`ISO/IEC 1539-1:2023` §19.5.3) + source (`gcc-mirror/gcc` @ `85ae7d8c...`, `gcc/fortran/trans-common.cc` L283–304)

Legacy Fortran 77 codebases share global mutable state via named/blank `COMMON /BLK/ A, B, C` blocks and intra-unit overlays via `EQUIVALENCE (A, B)`. Both rely on **storage sequence association** measured in *numeric storage units* (typically 4 bytes for default `INTEGER`/`REAL`/`LOGICAL`, 8 bytes for `DOUBLE PRECISION`/`COMPLEX`) and *character storage units* (1 byte).

In GFortran (`gcc/fortran/trans-common.cc` L283–304), `build_field()` merges all `EQUIVALENCE`-connected segments and `COMMON` members into a single GCC **`UNION_TYPE`** where each variable becomes a `FIELD_DECL` pinned at an explicit byte `offset` (`DECL_FIELD_OFFSET(field) = size_int(offset)`), setting `DECL_PACKED(field) = 1` whenever natural alignment exceeds `known_align = (offset & -offset) * BITS_PER_UNIT` (`L293–299`).

**Three FFI / soundness pitfalls**:
1. **Unaligned member accesses**: `EQUIVALENCE` or `COMMON` declarations that interleave `REAL(8)` after an odd count of `INTEGER(4)` produce 4-byte-aligned 8-byte floats (`DECL_PACKED`), violating strict C/Rust alignment invariants (`align_of::<f64>() == 8`) if cast directly to `&[f64]`.
2. **Cross-unit layout mismatch**: Two Fortran files can declare the *same* `COMMON /BLK/` with completely different member names, types, and even sizes (the linker allocates the maximum size among non-initialized `COMMON` symbols via ELF `STT_COMMON` / `SHN_COMMON`).
3. **Aliasing escape**: Two variables sharing a `COMMON`/`EQUIVALENCE` overlay alias each other even without `TARGET`, which optimizers must track carefully (`trans-common.cc` union layout vs Flang `AliasAnalysis`).

#### 4.3 `ISO_Fortran_binding.h` (`CFI_cdesc_t`) Dope Vectors and Cross-Compiler ABI Divergence

Basis: normative (`ISO/IEC 1539-1:2023` §18.5) + source (`llvm/llvm-project` @ `c85e6b92...`, `flang/include/flang/ISO_Fortran_binding.h` L33–55, L123–167; `gcc-mirror/gcc` @ `85ae7d8c...`, `libgfortran/ISO_Fortran_binding.h` L37–91)

Fortran 2018 (carried forward into Fortran 2023 §18.5) standardized `ISO_Fortran_binding.h` so C/Rust code can interoperate with Fortran assumed-shape (`A(:,:)`), assumed-rank (`A(..)`), `ALLOCATABLE`, and `POINTER` dummy arguments via a standard **dope vector** (`CFI_cdesc_t`).

Every dimension is described by `CFI_dim_t`:
```c
typedef struct CFI_dim_t {
    CFI_index_t lower_bound; /* ptrdiff_t: arbitrary signed lower bound (0 for non-pointer/non-allocatable dummies) */
    CFI_index_t extent;      /* ptrdiff_t: element count along this dim (-1 for assumed-size last dim) */
    CFI_index_t sm;          /* ptrdiff_t: SIGNED byte stride multiplier (may be negative or non-multiple of elem_len!) */
} CFI_dim_t;
```
**Crucial indexing properties**:
- Stride `sm` is in **bytes** (not elements) and is **signed** (`ptrdiff_t`): a reversed slice `A(10:1:-1)` passes `sm = -sizeof(T)`, and a struct-component slice `arr(:)%field` passes `sm = sizeof(struct)` where `sm > elem_len`. Element address for subscript tuple $(s_0, \dots, s_{r-1})$ is:
  $$\text{addr}(s) = \text{base\_addr} + \sum_{k=0}^{r-1} (s_k - \text{dim}[k].\text{lower\_bound}) \cdot \text{dim}[k].\text{sm}$$
- Memory layout is **column-major** by default for contiguous arrays: `dim[0].sm == elem_len`, `dim[1].sm == dim[0].extent * elem_len`, etc.
- `CFI_establish`, `CFI_allocate`, `CFI_deallocate`, `CFI_section`, and `CFI_setpointer` are the *only* standard-blessed ways for C code to construct or mutate descriptors; direct mutation of `base_addr`/`dim` by C code violates descriptor invariants (and Flang's `extra` allocator/addendum bits).

**CRITICAL FINDING — Cross-Compiler Binary ABI Incompatibility (`Basis: source`)**:
ISO/IEC 1539-1:2023 §18.5.3 mandates only that `base_addr`, `elem_len`, and `version` appear first in that order and `dim[]` appears last; the ordering, integer types, and macro numeric values of `rank`, `attribute`, `type`, `CFI_VERSION`, and extra implementation fields are **processor-dependent**. Direct inspection of pinned upstream headers reveals that **LLVM Flang and GCC GFortran have completely incompatible binary layouts for `CFI_cdesc_t`**:

| Descriptor Property | LLVM Flang (`flang/include/flang/ISO_Fortran_binding.h`, `c85e6b92...`) | GCC GFortran (`libgfortran/ISO_Fortran_binding.h`, `85ae7d8c...`) | Binary Interop Impact |
| :--- | :--- | :--- | :--- |
| `CFI_VERSION` | `20240719` (`L33`) | `1` (`L37`) | Version check rejects or misreads descriptor |
| `CFI_rank_t` | `unsigned char` (`L38`, 1 B) | `int8_t` (`L64`, 1 B) | Same width, signedness differs |
| **Field 5 (after `rank`)** | **`CFI_type_t type`** (`signed char`, 1 B, `L50`, `L154`) | **`CFI_attribute_t attribute`** (`int8_t`, 1 B, `L65`, `L87`) | **Swapped field offsets!** Reading `attribute` reads Flang's `type`! |
| **Field 6** | **`CFI_attribute_t attribute`** (`unsigned char`, 1 B, `L45`, `L155`) | **`CFI_type_t type`** (`int16_t`, **2 B**, `L66`, `L88`) | **Swapped order + 1 B vs 2 B width mismatch!** |
| **Extra Header Field** | `unsigned char extra` (`L158`, `f18Addendum` + allocator index) | *(none)* | Flang expects `extra` flags; GFortran leaves bytes uninitialized/used by `type` |
| `CFI_attribute_pointer` | `1` (`L46`) | `0` (`L41`) | **Enum collision**: GFortran `pointer` (`0`) == Flang `other` (`0`)! |
| `CFI_attribute_allocatable` | `2` (`L47`) | `1` (`L42`) | **Enum collision**: GFortran `allocatable` (`1`) == Flang `pointer` (`1`)! |
| `CFI_attribute_other` | `0` (`L48`) | `2` (`L43`) | **Enum collision**: GFortran `other` (`2`) == Flang `allocatable` (`2`)! |

**FFI Engineering Rule**: A C or Rust FFI crate MUST NEVER hardcode a single `#[repr(C)] struct CFI_cdesc_t` layout across toolchains; bindings must be generated (`bindgen`) against the exact target Fortran compiler's `ISO_Fortran_binding.h` and linked against that same compiler's Fortran runtime library (`libflang_rt` vs `libgfortran`).

---

### 5. MATLAB 1-Based Column-Major Copy-on-Write (CoW) MEX Boundaries

Basis: documentation (MathWorks C Matrix API, R2018a+ Interleaved Complex API, C++ MATLAB Data API) + derived

MATLAB's C MEX entry point has the signature:
```c
void mexFunction(int nlhs, mxArray *plhs[], int nrhs, const mxArray *prhs[]);
```

Crossing the MATLAB-to-C/Rust MEX boundary exposes **five load-bearing semantic traps**:

1. **1-Based Column-Major Memory Layout**:
   Like Fortran (MATLAB's original implementation language), an $M \times N$ matrix stores element $(i, j)$ (1-based: $1 \le i \le M, 1 \le j \le N$) at 0-based linear offset $(i - 1) + (j - 1) \cdot M$. Passing a C/Rust row-major 2D buffer to MATLAB without transposition silently transposes the matrix; higher-rank tensors vary fastest in the *first* index.
2. **Copy-on-Write (CoW) Workspace Sharing vs `const mxArray *prhs[]`**:
   When MATLAB executes `B = A; my_mex(B);`, `A` and `B` share the exact same heap data buffer via internal reference counting. The C Matrix API (`mex.h`) does **not** perform automatic CoW detachment when C code casts away `const` on `prhs[i]` (`double *p = mxGetDoubles(prhs[0]); p[0] = 99;`). Mutating `prhs[i]` in place **silently corrupts `A` in the caller's MATLAB workspace** (and breaks MATLAB JIT assumptions). Safe C MEX mutation requires either:
   - Allocating a fresh output (`mxCreateDoubleMatrix` / `mxDuplicateArray(prhs[i])`) and writing into `plhs[0]`; or
   - Using the modern **C++ MATLAB Data API** (`mex.hpp`, `matlab::data::TypedArray<double>`), whose move/write semantics check the internal CoW reference count and detach automatically before mutation.
3. **Separated vs Interleaved Complex ABI (`-R2017b` vs `-R2018a`)**:
   - **Pre-R2018a (`-R2017b` separated complex)**: A complex `mxArray` owns *two* disjoint buffers—real parts at `mxGetPr(a)` and imaginary parts at `mxGetPi(a)`.
   - **R2018a+ (`-R2018a` interleaved complex)**: Complex elements are stored contiguously as `struct { double real; double imag; }` (`mxComplexDouble` via `mxGetComplexDoubles(a)`), matching C99 `_Complex double`, C++ `std::complex<double>`, Rust `[f64; 2]`, and Fortran `COMPLEX(C_DOUBLE_COMPLEX)` / BLAS `zgemm`.
   - Linking object code compiled with `-R2017b` against `-R2018a` runtime expectations (or calling `mxGetPr` on an interleaved complex array under `-R2018a`) causes immediate runtime errors or memory corruption.
4. **Non-Local Error Unwinding (`mexErrMsgIdAndTxt`) and Allocator Ownership**:
   - Allocations made via `mxMalloc`/`mxCalloc`/`mxCreate*` are registered with MATLAB's per-call **MEX memory manager**: when `mexFunction` returns *or* aborts via `mexErrMsgIdAndTxt`, MATLAB automatically frees every temporary `mxArray`/buffer *not* placed into `plhs[]` and *not* marked persistent via `mexMakeMemoryPersistent` / `mexMakeArrayPersistent`.
   - Because `mexErrMsgIdAndTxt` transfers control immediately back to MATLAB via a non-local unwind (historically `longjmp` / host exception mechanism), calling it directly from inside C++ or Rust frames **skips stack unwinding (`Drop` / RAII destructors)**, leaking `std::malloc`, Rust `Box`/`Vec`, file descriptors, and mutex locks! C++/Rust MEX wrappers must catch all errors, release non-MEX resources cleanly, and invoke `mexErrMsgIdAndTxt` only at a trivial C-ABI boundary frame with zero live RAII guards.
5. **64-Bit Index Width (`mwSize` / `mwIndex`)**:
   Since R2017a (`-largeArrayDims` default), `mwSize` and `mwIndex` are 64-bit (`size_t`/`ptrdiff_t`), whereas legacy 32-bit BLAS/LAPACK symbols inside MATLAB's bundled `libmwblas`/`libmwlapack` use **ILP64** (`ptrdiff_t` 64-bit Fortran `INTEGER` arguments, unlike LP64 `int32_t` system BLAS!). Passing a 32-bit `int *` to MATLAB's bundled `dgemm_` reads 4 bytes of adjacent stack garbage as the upper 32 bits of matrix dimensions—a notorious crash when linking Rust/C MEX extensions against `libmwblas`.

## Boundaries

- **Direct compiler execution of `cobc`, `gfortran`, `flang`, `yottadb`, and `matlab` (`not examined`)**: None of those five toolchains were installed in the local execution environment. All compiler-internal claims are grounded in direct source inspection of pinned upstream commits (`OCamlPro/gnucobol4`, `YottaDB/YDB`, `llvm/llvm-project`, `gcc-mirror/gcc`) and official standards/documentation, supplemented by executable Python/C probes (`gcc 15.2.0`) reproducing the packed-BCD layout, MUMPS collation, and `restrict` aliasing mechanisms.
- **IBM Enterprise COBOL on z/OS binary internals (`not examined`)**: Proprietary IBM Enterprise COBOL compiler internals and hardware DFP (`IEEE 754-2008` decimal floating-point) code generation were not inspected; IBM z/OS `S0C7` Data Exception behavior is cited from standard z/Architecture / COBOL semantics and modeled in Probe A rather than executed on mainframe hardware.
- **GFortran `-fno-automatic` / `-faggressive-function-elimination` and Flang OpenMP/OpenACC alias extensions (`not examined`)**: Aliasing edge cases involving Fortran 2018/2023 `COARRAY` remote segments, `DO CONCURRENT`, and OpenMP `target` mapping were not analyzed in detail.
- **GNU Octave `mex.h` compatibility divergences (`not examined`)**: Octave implements a source-compatible subset of MATLAB's C Matrix API, but internal CoW detachment hooks, `-R2018a` interleaved complex defaults, and exception unwinding mechanisms in Octave were not inspected.
- **CFI ABI compatibility with third-party proprietary Fortran compilers (`unknown`)**: Layouts of `ISO_Fortran_binding.h` for Intel `ifx`/`ifort`, NVIDIA `nvfortran`, NAG Fortran, and Cray `ftn` were not inspected; given that ISO/IEC 1539-1:2023 leaves field order, `CFI_type_t`, and `CFI_attribute_*` processor-dependent, binary incompatibility with both Flang and GFortran should be assumed unless explicitly verified against each compiler's shipped header.
- **Stronger conclusion NOT established**: Using `ISO_C_BINDING` (`BIND(C)`) does **not** disable Fortran's dummy-argument non-aliasing rule on the Fortran side of the call, nor does it guarantee cross-compiler binary portability for `CFI_cdesc_t` descriptors.

## Evidence

### Normative Standards and Official Documentation
1. **ISO/IEC 1989:2023**, *Information technology — Programming languages, their environments and system software interfaces — Programming language COBOL* (3rd edition; `COMP-3` / `USAGE PACKED-DECIMAL` including `NO SIGN`, `REDEFINES`, `PERFORM ... THRU`, `ON SIZE ERROR`).
2. **ANSI/MDC X11.1-1995**, *Programming Languages — M (MUMPS)* (canonical numeric representation, subscript collation order, `^global` trees, `@` indirection, `TSTART`/`TCOMMIT`).
3. **ISO/IEC 1539-1:2023**, *Information technology — Programming languages — Fortran — Part 1: Base language* (§15.5.2.13 dummy-argument aliasing restrictions; §18.5 `ISO_Fortran_binding.h` C descriptors; §19.5.3 `COMMON`/`EQUIVALENCE` storage association).
4. **MathWorks MATLAB C Matrix API & Interleaved Complex API Documentation** (`https://www.mathworks.com/help/matlab/c-matrix-api.html`, R2018a+ `-R2018a` interleaved complex ABI, read-only `prhs` / `mxDuplicateArray` CoW contract, `mexErrMsgIdAndTxt` cleanup semantics).

### Pinned Upstream Source Inspections (Observed 2026-11-19)
- **`OCamlPro/gnucobol4` @ `780745d1bac79adea61808647f5a8e4b98bee8b0`**:
  - `libcob/numeric.c`: packed sign test `((p & 0x0F) == 0x0D) ? -1 : 1` (L970–974), `cob_decimal_set_packed` & `COB_FIELD_NO_SIGN_NIBBLE` / `COB_FIELD_SCALE` (L1144–1159), `cob_decimal_get_packed` with GMP `mpz_sgn`/`mpz_abs` (L1249–1264).
  - `cobc/field.c`: `cb_resolve_redefines` (L616–631), `CB_USAGE_PACKED` / `CB_USAGE_COMP_6` handling (L973–975).
  - `cobc/codegen.c`: `frame_ptr->return_address_num` dispatch labels (L1393–1408), `output_perform_call` (`ALTER` segment label save/zap L7267–7314; `frame_ptr++`, `frame_ptr->perform_through = le->id`, computed `goto` / `return_address_ptr`, `frame_ptr--` L7321–7359), `output_perform_once` (L7561–7572).
- **`YottaDB/YDB` @ `7a1fee723cd0d2b4c127e9c670ccc72041ec4bb0`**:
  - `sr_port/mval2subsc.c`: `mval2subsc` (L62–83), `STR_SUB_PREFIX` / `STR_SUB_ESCAPE` string encoding & `GVSUBOFLOW` (L128–150), `SUBSCRIPT_ZERO` (L178), `pos_code`/`neg_code` & `~(exp_val)` negative inversion for bytewise B-tree collation (L170–260).
  - `sr_port/op_indname.c`: `op_indname` runtime `@` indirection string coercion, quote-aware `;` comment scan, and `ERR_INDRMAXLEN` (L31–52).
  - `sr_port/t_end.c`: `t_end` optimistic transaction validation (`srch_hist`, `cw_set_element`, `cdb_sc_*` retry codes, `CDB_STAGNATE` crit escalation, L196–217, L295–317).
- **`llvm/llvm-project` @ `c85e6b928dfd2552497fe666f281f3d49c2c0f70` (`flang`)**:
  - `flang/include/flang/ISO_Fortran_binding.h`: `CFI_VERSION = 20240719` (L33), `CFI_rank_t = unsigned char` (L38), `CFI_attribute_t = unsigned char` with `other=0, pointer=1, allocatable=2` (L45–48), `CFI_type_t = signed char` (L50), `CFI_dim_t` (L123–127), `_CFI_CDESC_T_HEADER_MEMBERS` (`base_addr, elem_len, version, rank, type, attribute, extra`, L147–158), `CFI_cdesc_t` (L160–167).
  - `flang/lib/Optimizer/Analysis/AliasAnalysis.cpp`: `-unsafe-cray-pointers` (L40–43), `isDummyArgument` (L494–496), `AliasAnalysis::alias` `SourceKind::Argument` vs `HostAssoc` (F18 §15.5.2.13(4)(b)) and `TARGET`/`POINTER` non-aliasing rules (L995–1065).
- **`gcc-mirror/gcc` @ `85ae7d8c7c16d1ad96c2e19e17f2e2aa739bd72e` (`gcc/fortran`, `libgfortran`)**:
  - `libgfortran/ISO_Fortran_binding.h`: `CFI_VERSION = 1` (L37), `CFI_attribute_pointer=0, allocatable=1, other=2` (L41–43), `CFI_rank_t = int8_t`, `CFI_attribute_t = int8_t`, `CFI_type_t = int16_t` (L64–66), `CFI_dim_t` (L69–75), `CFI_cdesc_t` (`base_addr, elem_len, version, rank, attribute, type, dim[]`, L81–91).
  - `gcc/fortran/trans-types.cc`: `TYPE_QUAL_RESTRICT` on `prvoid_type_node` (L1198), `GFC_TYPE_ARRAY_DATAPTR_TYPE` (L1939–1944), and rank-0 dummy pointer types (L1952–1953).
  - `gcc/fortran/trans-common.cc`: `build_field` laying out `COMMON`/`EQUIVALENCE` members as byte-offset `FIELD_DECL`s inside a `UNION_TYPE` with `DECL_PACKED` on under-aligned offsets (L283–304).

### Local Execution Probes (Observed 2026-11-19, Linux x86-64, GCC 15.2.0 & Python 3)
- **Probe A (`COMP-3` encoding & `REDEFINES` invalid-BCD check)**:
  - `12345` (`PIC S9(5) COMP-3`) -> `12345c` (3 bytes); `-12345` -> `12345d`; unsigned `12345` (`PIC 9(5) COMP-3`) -> `12345f`; overflow `123456` into `PIC S9(5) COMP-3` -> silent left truncation to `23456c` (`23456`).
  - `REDEFINES` overlay bytes: ASCII `"123"` (`313233`) -> invalid sign nibble `0x3`; EBCDIC `"123"` (`f1f2f3`) -> invalid digit nibbles `['0xf', '0xf', '0xf']`; ASCII/EBCDIC spaces (`202020` / `404040`) -> invalid sign nibble `0x0`.
- **Probe B (MUMPS ANSI X11.1 canonical numeric collation)**:
  - Input `["10","2","01","-2","-10","0",".5","0.5","1.0","1a","A","","-.5","+2"]`:
    - ASCII order: `['', '+2', '-.5', '-10', '-2', '.5', '0', '0.5', '01', '1.0', '10', '1a', '2', 'A']`
    - MUMPS order: `['', '-10', '-2', '-.5', '0', '.5', '2', '10', '+2', '0.5', '01', '1.0', '1a', 'A']`
- **Probe C (GCC 15.2.0 `-O2` Fortran-style `restrict` aliasing miscompilation)**:
  - Compiling `void f(int n, int *restrict out, const int *restrict in) { for (int i=0;i<n;i++) out[i] = in[i] + in[0]; }` vs non-`restrict` with `gcc -O2` and invoking both on `a = {10, 1, 2, 3}` with `out == in == a`:
    - `restrict_aliased`: `20 11 12 13` (hoisted `in[0] == 10`)
    - `normal_aliased`: `20 21 22 23` (observed `a[0]` updated to `20`)

## Revalidation

1. **Fortran `CFI_cdesc_t` ABI check**: On any target toolchain, compile a 10-line C program printing `offsetof(CFI_cdesc_t, rank)`, `offsetof(CFI_cdesc_t, attribute)`, `offsetof(CFI_cdesc_t, type)`, `sizeof(CFI_type_t)`, `CFI_VERSION`, and `(CFI_attribute_pointer, CFI_attribute_allocatable, CFI_attribute_other)` against the compiler's own `ISO_Fortran_binding.h` before generating or updating FFI bindings.
2. **Fortran dummy-argument aliasing & copy-in/copy-out check**: Compile a minimal Fortran subroutine `subroutine f(out, in); integer :: out(:), in(:); out = in + in(1); end` with the target compiler (`gfortran -O2` or `flang -O2`), inspect LLVM IR / GIMPLE for `noalias` / `restrict`, and verify whether passing `A(1:10:2)` to an explicit-shape callee triggers `-Warray-temporaries` / runtime temporary copy.
3. **COBOL `COMP-3` & `PERFORM THRU` check**: With `cobc -C` (emit C source), inspect the generated C for `cob_decimal_set_packed` calls and `frame_ptr->perform_through` assignments on overlapping `PERFORM A THRU B` test programs, and verify `IS NUMERIC` behavior on `REDEFINES` overlays.
4. **YottaDB subscript & OCC check**: In a live YottaDB environment (`yottadb -direct`), set `^T("01")=1,^T(10)=2,^T("0.5")=3,^T(".5")=4` and traverse with `$ORDER(^T(""))` to confirm canonical numeric ordering, and inspect `$TRESTART` under concurrent `TSTART`/`TCOMMIT` writers.
5. **MATLAB MEX CoW & complex ABI check**: Compile a test MEX file with `mex -R2018a` (checking `mxIsComplex` + `mxGetComplexDoubles`) and verify that `B = A; out = my_mex(B); isequal(A, orig)` holds before and after mutation, confirming no `prhs` in-place write occurs.
