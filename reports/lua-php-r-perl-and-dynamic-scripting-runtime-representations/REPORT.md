# Dynamic Scripting Runtime Representations: Lua/LuaJIT, PHP Zend Engine, R/RIR, and Perl 5

## Summary

Dynamic scripting runtimes diverge sharply in value representation, aliasing semantics, evaluation strategy, and call-context dispatch, producing distinct failure modes at compiler-optimization and foreign-function-interface (FFI) boundaries:

1. **Lua 5.5 vs. LuaJIT 2.1 (`LJ_GC64`)**: PUC-Rio Lua 5.5.1 uses a 16-byte tagged union `TValue` (safe against arbitrary IEEE-754 bit patterns and exact 64-bit `lua_Integer` values) while compressing table array slots to 9 bytes via an inverted-value/packed-tag bidirectional buffer (`Table.array`). LuaJIT 2.1 packs every value into an 8-byte NaN-boxed `TValue` (`LJ_GC64`: 13 sign/exponent ones, 4-bit tag, 47-bit payload; segmented 8+39-bit `lightuserdata`) with trace-JIT allocation sinking (`RID_SINK`) materialized lazily on guard-failure snapshots (`lj_snap_restore`). Crucially, LuaJIT's C-to-Lua FFI converter `lj_cconv_tv_ct` does **not** canonicalize `double` bit patterns in release builds (`lj_assertCTS` only), so reading an uninitialized or crafted negative IEEE-754 NaN (`0xfffa...`) from C memory can forge a tagged `GCobj*` pointer inside Lua.
2. **PHP Zend Engine (`php-src` 8.x)**: Zend stores values in 16-byte stack/bucket `zval` slots with Copy-on-Write (CoW) reference counting (`SEPARATE_ARRAY`, `SEPARATE_STRING`) for value assignments, but boxes `$a = &$b` aliases inside heap-allocated `zend_reference` wrappers (`IS_REFERENCE`) carrying typed-property source lists. During CoW array duplication (`zend_array_dup_value`), an inner `IS_REFERENCE` element is unwrapped **only** if its refcount equals `1` (and it does not point directly back to the containing array); any active external alias (`refcount > 1`) causes the reference wrapper itself to be shared into the duplicated array, breaking outer array value-copy isolation.
3. **GNU R and RIR/PIR**: GNU R implements call-by-need function arguments via heap-allocated `PROMSXP` thunks (`{value, expr, env}` with `PRSEEN` recursion-cycle detection in `forcePromise`) combined with first-class mutable environments (`ENVSXP`) and call-stack reflection (`RCNTXT`, `substitute()`, `parent.frame()`). Because any callee may inspect unevaluated `PRCODE` ASTs or mutate caller frames, sound JIT compilation in RIR/PIR requires contextual dispatch (`TypeAssumption` / `Assumption` specialization vectors), force-dominance promise inlining that preserves leaked environments, and checkpoint/deoptimization guards (`ElideEnvSpec`) whenever reflective primitives or S3/S4 objects appear.
4. **Perl 5**: Perl stores scalars in dynamically upgradable multi-slot `SV` headers with independent numeric/string/reference validity bits (`SVf_IOK`, `SVf_NOK`, `SVf_POK`, `SVf_ROK`), permitting contradictory dualvars (`dualvar(42, "forty-two")`). Call sites encode tri-state context (`G_VOID`, `G_SCALAR`, `G_LIST`) via `OPf_WANT_*` flags exposed dynamically through `wantarray`, creating list-context key-injection hazards in hash constructors (`key => fn()`). Arbitrary variables can carry `MAGIC` linked lists (`tie` via `PL_vtbl_packelem` / `PERL_MAGIC_tiedscalar` `'q'` and `PERL_MAGIC_tiedelem` `'p'`, plus Perl 5.45's `MGf_MGv2` v2 magic) that execute arbitrary re-entrant Perl callbacks during seemingly pure reads (`SvPV`, `SvIV`, `defined`), invalidating cached XS/C-API stack pointers (`dSP`/`ST(i)`) when `PL_stack_base` reallocates.

## Applicability

This report characterizes the runtime value layouts, aliasing/evaluation invariants, JIT/deoptimization interfaces, and C/FFI boundaries of six pinned upstream source trees and one live host runtime binary:

- **PUC-Rio Lua 5.5.1** (`lua/lua` at `c42d820bc0c3bc4f2ad536e19d2f05405af10387`): inspected for `TValue`, `Table` split-array layout, and metatable fast-cache mechanics. The 9-byte split-array layout in `ltable.h` is specific to Lua 5.5+; Lua 5.4 and earlier stored `TValue *array` directly (16 bytes/slot on 64-bit).
- **LuaJIT 2.1.ROLLING** (`LuaJIT/LuaJIT` branch `v2.1` at `63c8f1a9b479ba5518cf6a170ff7729178bc3cfd`): inspected for `TValue` NaN-boxing in both `LJ_GC64` (default on modern 64-bit x86-64/ARM64 builds) and `!LJ_GC64` (32-bit GC references / legacy 64-bit 2 GiB arena builds), `LJ_DUALNUM`, trace snapshots, allocation sinking, metatable caching, and FFI `cdata`/callback handling.
- **PHP Zend Engine 8.7.0-dev** (`php/php-src` at `e709ba4099085a5ee6a15846c32110873a15474a`): inspected for 64-bit LP64 (`SIZEOF_SIZE_T == 8`) `zval`, `zend_reference`, `HashTable` packed/hash layouts, and `SEPARATE_ARRAY` / `zend_array_dup_value` semantics. The 16-byte `zval` and `zend_reference` architecture originated in PHP 7.0 (with `sources` typed-property lists added in PHP 7.4 and `arPacked` separation in PHP 8.2); exact bit-field positions and `_IS_PLACEHOLDER` constants reflect the pinned 8.7.0-dev tree.
- **GNU R 4.7.0-devel** (`wch/r-source` at `94152790dbd49be40c28c1819f92370fb7581f0a`) and **RIR/PIR** (`reactorlabs/rir` at `affbfc2feec0263ecb9c83b181d1b06388283340`): examined together as a reference interpreter and a specializing JIT compiler targeting the same R language semantics. `SEXPREC`/`PROMSXP`/`forcePromise`/`do_substitute`/`do_parentframe` reflect GNU R 4.x (`SWITCH_TO_REFCNT` enabled); RIR/PIR optimization passes reflect the pinned `reactorlabs/rir` commit and its published DLS 2019 / OOPSLA 2020 designs.
- **Perl 5.45.5 (`blead`)** (`Perl/perl5` at `40d4fc76b5f9cab20ca3914d2aa017863230719b`) and **Perl 5.40.1** (`x86_64-linux-gnu-thread-multi` host binary): source claims about `SV` layout, `OPf_WANT_*`, `pp_wantarray`, `MGVTBL`, and `Perl_mg_get`/`Perl_mg_set` are anchored in `blead` 5.45.5, while `MGf_MGv2` (`MgIsV2`) is specific to newer 5.45 development code. Live execution observations (`wantarray`, `tie`, `Devel::Peek::Dump`) were executed on Perl 5.40.1.

Claims from Python bit-level and state-machine micro-probes verify exact transcriptions of pinned C macros and functions (`lj_obj.h`, `zend_types.h`, `zend_hash.c`); they are labeled `execution` (executable model) + `source` and do not substitute for executing compiled LuaJIT or PHP binaries. All structural sizes assume 64-bit little-endian LP64 platforms unless explicitly noted.

## Findings

### 1. Cross-Runtime Architectural Trade-off Matrix

Basis: source + documentation + derived

| Dimension | PUC-Rio Lua 5.5.1 | LuaJIT 2.1 (`LJ_GC64`) | PHP Zend Engine 8.x | GNU R 4.x (+ RIR/PIR) | Perl 5.4x |
|---|---|---|---|---|---|
| **Primary value slot** | 16 B `TValue` (`Value` 8 B + `lu_byte tt_` + pad) | 8 B NaN-boxed `TValue` (`uint64_t`: 13 ones + 4-bit tag + 47-bit payload) | 16 B `zval` (`zend_value` 8 B + `u1.type_info` 4 B + `u2` 4 B) | Heap `SEXPREC` pointer (`SEXP`, 8 B); 56 B / 48 B node headers on 64-bit | Heap `SV*` pointer (8 B); `struct sv` head + upgradable `XPV*` body |
| **Numeric duality** | Separate `LUA_VNUMINT` (`int64_t`) & `LUA_VNUMFLT` (`double`) | `double` primary; optional `int32_t` via `LJ_DUALNUM` (`LJ_TISNUM`) | Separate `IS_LONG` (`zend_long`) & `IS_DOUBLE` (`double`) | Typed homogeneous vectors (`INTSXP` 32-bit w/ `NA_INTEGER`, `REALSXP` `double`) | Multi-slot simultaneous `IV`/`UV`, `NV`, `PV` with independent `SVf_IOK`/`NOK`/`POK` flags |
| **Aggregate / container** | Hybrid `Table`: split 9 B/slot inverted `Value`+tag array + open-addressing `Node` hash | Hybrid `GCtab`: 8 B/slot `TValue` array + `Node` hash | Ordered `HashTable`: packed `arPacked` (16 B/slot `zval`) or `arData` (`Bucket`) + negative `arHash` | Vector `VECTOR_SEXPREC` + pairlists (`LISTSXP`) + `ENVSXP` hash frames | `AV` (`XPVAV` dynamic `SV**`), `HV` (`XPVHV` chained hash of `HE` entries) |
| **Aliasing & mutation** | Reference semantics for tables/userdata; immutable interned strings | Same as Lua; `cdata` pointers alias raw C memory | Value semantics + CoW (`GC_REFCOUNT > 1` -> `SEPARATE_ARRAY`); explicit `$a = &$b` boxes `zend_reference` | Value semantics + `REFCNT`/`MAYBE_SHARED` CoW; `ENVSXP` has reference semantics | Reference/alias semantics in `@_`, `foreach`, `\$x`; CoW string buffers (`SVf_IsCOW`) |
| **Evaluation & dispatch** | Strict call-by-value; per-table/userdata metatable (`nomm` 6-bit fast cache) | Strict call-by-value; metatable + trace-specialized FFI `cdata` metamethods | Strict call-by-value unless parameter declared `&` (pass-by-ref) | **Call-by-need** (`PROMSXP` thunks) + NSE (`substitute()`, `parent.frame()`) | Strict + **tri-state call context** (`G_VOID`/`G_SCALAR`/`G_LIST`, `wantarray`) + `MAGIC` hooks |
| **JIT & deoptimization** | Bytecode VM only (no built-in JIT) | Trace-recording JIT (`GCtrace`), `SnapShot` side-exits, `RID_SINK` allocation sinking | Tracing/function JIT in `ext/opcache` (outside core VM scope) | GNU R bytecode (`bcEval`); **RIR/PIR** contextual specialization + `Checkpoint`/`Deopt` | Op-tree interpreter (`runops`), no built-in JIT |
| **FFI / C-API root contract** | Explicit stack-slot C API (`lua_State*`); full userdata GC-managed | Direct FFI (`ffi.cdef`/`cdata`) bypassing `lua_State`; `ffi.cast` does **not** root memory | Explicit `zval` refcounting (`Z_ADDREF_P`, `SEPARATE_ZVAL`) + `ext/ffi` | Manual `PROTECT`/`UNPROTECT` stack for `SEXP`s; GC runs on allocation | Manual `SvREFCNT` + mortal stack; `dSP`/`SPAGAIN` across re-entrant magic/callbacks |
| **Signature soundness / semantic hazard** | Metatable cycles & `__gc` resurrection (safe value tagging) | Unsanitized FFI `double` NaN -> forged `GCobj*`; `ffi.cast` UAF; callback slot exhaustion | Nested `IS_REFERENCE` survives `SEPARATE_ARRAY` when `rc > 1` | `substitute()`/`parent.frame()` invalidates promise elision & env erasure | List-context hash-key injection; `tie` `FETCH` re-entrancy reallocating XS stack |

---

### 2. PUC-Rio Lua 5.5 and LuaJIT 2.1: Tagged Unions vs. NaN-Boxing, Trace-JIT Snapshots, Metatables, and FFI

#### 2.1 Value Layout: Lua 5.5.1 Split-Array Tagged Values vs. LuaJIT 2.1 NaN-Boxing

Basis: source + execution (executable bit model)

PUC-Rio Lua 5.5.1 (`lua/lua`, `lobject.h:49-78`) keeps a clean separation between payload and type tag:

```c
typedef union Value {
  struct GCObject *gc;    /* collectable objects */
  void *p;                /* light userdata */
  lua_CFunction f;        /* light C functions */
  lua_Integer i;          /* integer numbers (64-bit by default) */
  lua_Number n;           /* float numbers (IEEE-754 double) */
  lu_byte ub;
} Value;

#define TValuefields  Value value_; lu_byte tt_
typedef struct TValue { TValuefields; } TValue;
```

On 64-bit architectures, `TValue` is 16 bytes (8 bytes `Value`, 1 byte `tt_`, 7 bytes struct padding). Because the tag `tt_` lives outside the 64-bit `Value` union, Lua 5.5 natively represents full 64-bit signed integers (`LUA_VNUMINT`), full 64-bit pointers, and arbitrary IEEE-754 `double` bit patterns (including signaling/non-canonical NaNs) without any tagging collisions.

To eliminate the 7-byte per-element padding overhead in array-heavy tables without sacrificing out-of-band tagging, Lua 5.5 (`ltable.h:95-125`, `lobject.h:777-786`) stores a `Table`'s array part as an **inverted `Value` array followed by an inline `unsigned` length hint and a dense `lu_byte` tag array**, with `Table.array` pointing directly between the two regions:

```text
          Values (negative indices)                 Tags (non-negative indices)
  -------------------------------------------------------------------------------
  ... | Value[1] (8 B) | Value[0] (8 B) | lenhint (4 B) | tag[0] | tag[1] | ...
  -------------------------------------------------------------------------------
                                        ^ t->array
  getArrVal(t, k) := (t)->array - 1 - (k)
  getArrTag(t, k) := (lu_byte*)(t)->array + sizeof(unsigned) + (k)
```

This reduces array storage from 16 bytes/element (Lua 5.4) to **9 bytes/element** (+ 4 bytes once per table) while preserving full 64-bit integers and exact NaN safety. Hash nodes (`union Node`, `lobject.h:752-760`) similarly pack `key_tt` (1 byte) and `int next` (4 bytes) into the padding after `TValuefields`, keeping `Node` at 24 bytes instead of 32.

In contrast, **LuaJIT 2.1** (`LuaJIT/LuaJIT`, `src/lj_obj.h:174-298`) compresses every `TValue` to **8 bytes** via IEEE-754 **NaN-boxing** (overlapping tags with negative quiet NaNs whose upper bits exceed the hardware-generated canonical quiet NaN `0xfff8_0000_0000_0000`):

- **32-bit GC reference mode (`!LJ_GC64`)** (`lj_obj.h:226-241, 277-281`): the 32-bit MSW (`u32.hi` / `it`) stores `itype` and the 32-bit LSW (`u32.lo`) stores a 32-bit `GCRef` (forcing all GC objects into the low 2 GiB address space on legacy x86-64 builds) or `int32_t` (`LJ_DUALNUM`). On `LJ_64 && !LJ_GC64`, `LJ_TISNUM = 0xfffeffffu`, and `lightuserdata` encodes a 47-bit segmented pointer across `0xffff | seg (8 bits) | ofs (39 bits)`.
- **64-bit GC reference mode (`LJ_GC64`)** (`lj_obj.h:73-75, 242-298, 783-813`): the upper 13 bits are all `1` (`0xfff8...`), the next 4 bits hold the inverted internal tag, and the lowest 47 bits (`LJ_GCVMASK = (1ULL << 47) - 1`) hold a 47-bit user-space pointer (`GCRef`), a zero-extended `int32_t`, all-ones for primitives (`nil`/`false`/`true`), or segmented `lightuserdata` (`LJ_LIGHTUD_BITS_SEG = 8` segment index + `LJ_LIGHTUD_BITS_LO = 39`, i.e., 256 segments of 512 GiB each, mapped via `GCState.lightudseg`).

The tag ordering (`lj_obj.h:260-285`) uses small negative 32-bit integers (`~0u` down to `~13u`) so type checks compile to a single sign-extended immediate compare:

| Tag Constant | Unsigned 32-bit Value | `LJ_GC64` Top 17 Bits | Meaning / Range Check (`lj_obj.h:783-813`) |
|---|---|---|---|
| `LJ_TNIL` | `~0u` (`0xffffffff`) | `0x1ffff` (`it64 == -1`) | `nil`; `tvisnil(o)` |
| `LJ_TFALSE` | `~1u` (`0xfffffffe`) | `0x1fffe` | `false`; `tvistruecond(o) := itype(o) < LJ_TFALSE` |
| `LJ_TTRUE` | `~2u` (`0xfffffffd`) | `0x1fffd` | `true`; `tvispri(o) := itype(o) >= LJ_TTRUE` |
| `LJ_TLIGHTUD` | `~3u` (`0xfffffffc`) | `0x1fffc` | Segmented 8+39-bit light userdata (`LJ_KEYINDEX = 0xfffe7fffu` traversal sentinel) |
| `LJ_TSTR`..`LJ_TUDATA` | `~4u`..`~12u` (`0xfffffffb`..`0xfffffff3`) | `0x1fffb`..`0x1fff3` | GC objects: `STR`, `UPVAL`, `THREAD`, `PROTO`, `FUNC`, `TRACE`, `CDATA` (`~10u`), `TAB` (`~11u`), `UDATA` (`~12u`) |
| `LJ_TNUMX` / `LJ_TISNUM` | `~13u` (`0xfffffff2`) | `0x1fff2` | `LJ_DUALNUM` integer (`itype == LJ_TISNUM`); doubles satisfy **`itype(o) < LJ_TISNUM`** |
| Canonical qNaN | `0xfffffff0` (`~15u`) | `0x1fff0` (`0xfff80000_00000000`) | `setnanV(o)`: canonical IEEE-754 NaN (`< LJ_TISNUM`!) |

The key bit-twiddling subtlety in `LJ_GC64` (`lj_obj.h:784, 807`) is that `itype(o)` performs a **signed arithmetic right shift** on `int64_t it64` and casts the result to **`uint32_t`**:

```c
#define itype(o)    ((uint32_t)((o)->it64 >> 47))
#define tvisnum(o)  (itype(o) < LJ_TISNUM)   /* unsigned < 0xfffffff2u */
```

For all non-negative doubles (`+0.0`, `3.14`, `+inf`, positive NaNs), sign bit 63 is `0`, so `itype(o) ∈ [0x00000000, 0x0000ffff] < 0xfffffff2u`. For all negative finite doubles, `-inf`, and the x86-64 canonical quiet NaN (`0xfff8000000000000`), sign bit 63 is `1` and `itype(o) ∈ [0xffff0000, 0xfffffff0] < 0xfffffff2u`. Only bit patterns with top 17 bits `>= 0x1fff2` (i.e., `u64 >= 0xfff9_0000_0000_0000`) are interpreted as tagged integers or non-numeric types.

#### 2.2 NaN-Boxing Soundness Hazard Across the LuaJIT FFI Boundary

Basis: source + execution (executable bit model)

Because `LJ_GC64` repurposes IEEE-754 negative quiet NaN payloads (`0xfff9_8000_0000_0000` through `0xffff_ffff_ffff_ffff`) as tagged pointers (`LJ_TUDATA` through `LJ_TNIL`), soundness of LuaJIT's heap requires the invariant that **no uncanonicalized negative NaN ever enters a `TValue` slot**. Yet direct inspection of `src/lj_cconv.c:380-405` (`lj_cconv_tv_ct`) proves that LuaJIT deliberately omits NaN canonicalization when loading a C `double` into a Lua `TValue`:

```c
/* LuaJIT/LuaJIT src/lj_cconv.c:396-400 */
lj_cconv_ct_ct(cts, ctype_get(cts, CTID_DOUBLE), s,
               (uint8_t *)&o->n, sp, 0);
/* Numbers are NOT canonicalized here! Beware of uninitialized data. */
lj_assertCTS(tvisnum(o), "non-canonical NaN passed");
```

In production builds (`LUA_USE_ASSERT` disabled), `lj_assertCTS` compiles to a no-op. Consequently, if C code, deserialized binary data, or uninitialized stack/heap memory passes a `double` whose raw bit pattern is `0xfffa_0000_dead_beef`, the executable bit model confirms `itype_gc64(0xfffa0000deadbeef) = 0xfffffff4 = ~11u = LJ_TTAB` with 47-bit `GCtab*` payload `0x00000000deadbeef`. LuaJIT then treats that attacker-controlled or uninitialized address as a live garbage-collected Lua table, causing immediate type confusion, GC heap corruption, or arbitrary memory read/write. Verification and FFI wrappers targeting LuaJIT must canonicalize every floating-point value crossing from untrusted C memory (`if (d != d) d = canonical_qnan`) before handing it to LuaJIT `TValue` conversion.

#### 2.3 Trace-JIT Side-Exit Snapshots and Allocation Sinking

Basis: source + documentation

LuaJIT's JIT compiler (`lj_jit.h:217-313`, `lj_trace.c`, `lj_record.c`, `lj_opt_sink.c`, `lj_snap.c`) is a **trace-recording** compiler (building on Gal et al., PLDI 2009): when a loop header or function entry hits its hotcount threshold, the recorder executes bytecode in the interpreter while emitting SSA IR (`IRIns` array in `GCtrace.ir`, biased by `REF_BIAS`) along the hot dynamic path and inserting type/value/shape guards.

To decouple optimized machine code from interpreter frame layouts, LuaJIT attaches a compact table of **snapshots** (`GCtrace.snap` indexing into `GCtrace.snapmap`) at guard sites:

- Each `SnapShot` records `mapofs` (offset into `snapmap`), `ref` (IR boundary), `nent` (number of modified Lua stack slots), and frame-link entries (`SNAP_FRAME`, `snap_pc` recovering the exact interpreter `BCIns*` PC). Unmodified slots are omitted (sparse snapshots).
- When a guard fails at runtime, the exit stub saves all architectural GPRs and FPRs into an `ExitState` struct and calls `lj_snap_restore(J, exptr)` (`lj_snap.c:940-965`), which walks the failing snapshot's `SnapEntry` records, writes reconstructed `TValue`s back onto `L->base` / `L->top`, restores `L->cframe` PC (`pc` for returns/tailcalls, `pc+1` otherwise), and resumes the bytecode interpreter at the exact failing instruction.
- **Allocation Sinking (`lj_opt_sink.c`, `lj_snap.c:860-937`)**: Escape analysis marks non-escaping temporary allocations (`IR_TNEW`, `IR_TDUP`, FFI `IR_CNEW`/`IR_CNEWI` `cdata` boxes) and their stores (`IR_ASTORE`, `IR_HSTORE`, `IR_FSTORE`, `IR_XSTORE`) with register tag **`RID_SINK`**. The fast compiled loop performs **zero heap allocations** (keeping fields scalarized in CPU registers). Only if a side-exit triggers does `snap_unsink` (`lj_snap.c:860-937`) materialize the `GCtab` (`lj_tab_new`/`lj_tab_dup`) or `GCcdata` on the heap and replay every `RID_SINK` store (including `IRFL_TAB_META` metatable writes and `IR_XSTORE` C struct fields at constant offsets) into the newly allocated object before entering the interpreter.
- **Side traces, trace stitching, and NYI aborts (`lj_jit.h:237-312`, `lj_traceerr.h`)**: Repeated side-exits from the same snapshot trigger recording of a **side trace** (`GCtrace.root != 0`) linked directly off the guard stub (`LJ_TRLINK_ROOT`, `LJ_TRLINK_LOOP`, `LJ_TRLINK_STITCH`). However, encountering an unrecorded bytecode, C function, or unsupported FFI signature aborts the trace (`LJ_TRERR_NYIBC`, `NYIFFU`, `NYIRETL`, `NYITMIX`, `NYICONV`, `NYICALL`) and inserts the starting PC into the 64-slot `HotPenalty` cache (`PENALTY_MIN = 72` up to `PENALTY_MAX = 60000`, backing off exponentially to prevent thrashing). Subtle code patterns (such as `pairs()` in older LuaJIT, `pcall` across frames, `next()`, or mixed sparse/dense tables) silently collapse hot loops back to interpreter speed via NYI aborts.

#### 2.4 Metatable Dispatch and Negative Caching

Basis: source

Both PUC-Rio Lua (`ltm.h:19-68`, `ltm.c:50-85`) and LuaJIT (`lj_meta.c:57-520`) accelerate hot operations (table indexing, length, equality, arithmetic) with a **negative metamethod cache** stored in a 1-byte bitfield on every `Table`/`GCtab` (`flags` in Lua 5.5, `nomm` in LuaJIT):

- The 6 lowest bits (`TM_INDEX` through `TM_EQ` in Lua `ltm.h:19-24, 54`: `maskflags = ~(~0u << (TM_EQ + 1))`) cache the **absence** of fast-access metamethods. On the first failed lookup (`luaT_gettm`, `ltm.c:63-64`; `lj_meta.c:57`), bit `1u << event` is set. Subsequent accesses check `(mt->flags & (1u << event))` in a single branch without hashing `"__index"` or `"__newindex"`.
- **Cache invalidation**: Any write to a table that might serve as a metatable clears the cache (`invalidateTMcache(t)` in Lua `ltable.h:23`; `t->nomm = 0` in `lj_meta.c:176, 180`). Mutating a metatable at runtime therefore forces re-lookup and invalidates JIT-recorded constant-metatable guards.
- Lua 5.5 adds `TM_CLOSE` (`ltm.h:43`) for `<close>` to-be-closed deterministic scope exit; LuaJIT 2.1 targets Lua 5.1/5.2 semantics and additionally supports metamethods on `cdata` types via `ffi.metatype` (checked in `lj_meta.c:464`), which are compiled into traces as type-specialized direct calls when monomorphic.

#### 2.5 LuaJIT FFI `cdata` Layout, Direct Trace Compilation, and Lifetime Hazards

Basis: source + documentation

LuaJIT's FFI (`lj_obj.h:348-365`, `lj_cdata.h`, `lj_crecord.c:1123-1350`, `lj_ccallback.c:26-80`) embeds C type descriptors (`CTState`/`CType`) directly inside the runtime:

- **Memory layout**: Fixed-size C objects use `GCcdata { GCHeader; uint16_t ctypeid; }` with raw C payload immediately following at `cdataptr(cd) = (void *)(cd + 1)`. Variable-length arrays and over-aligned allocations (`cdataisv(cd) := cd->marked & 0x80`) prepend a `GCcdataVar { uint16_t offset; uint16_t extra; MSize len; }` header immediately before `GCcdata` so `memcdatav(cd)` can recover the aligned base allocation pointer.
- **Zero-overhead trace calls**: Unlike the standard Lua C API (which marshals every argument through `lua_State`'s `TValue` stack), `recff_cdata_call` -> `crec_call` (`lj_crecord.c:1266-1350`) lowers C function calls directly into SSA IR `IR_CALLXS` instructions conforming to the native platform C ABI, eliminating stack marshaling and `TValue` boxing inside loops.
- **GC rooting hazard (`ffi.cast` and interior pointers)**: `ffi.new("uint8_t[1024]")` allocates a GC-managed `GCcdata` object, whereas `ffi.cast("uint8_t*", buf + 16)` or storing `buf` into a C struct pointer field produces a raw `cdata` pointer that does **not** hold a GC reference to `buf`. If the original Lua `cdata` reference goes dead, LuaJIT's incremental GC frees the backing buffer while the derived pointer remains live, causing use-after-free. Calling `ffi.gc(ptr, finalizer)` registers a finalizer on the `GCcdata` wrapper (`lj_cdata_setfin`, `lj_cdata.h:68`), **not** on arbitrary derived pointers.
- **Callback trampoline exhaustion and JIT exclusion (`lj_ccallback.c:26-80`)**: Passing a Lua function as a C function pointer allocates a fixed machine-code trampoline slot from a bounded executable page pool (`CALLBACK_MCODE_SIZE = LJ_PAGESIZE * LJ_NUM_CBPAGE`, bounded by `CALLBACK_MAX_SLOT`, typically a few hundred slots on x86-64). Calling into a Lua callback from C is **never JIT-compiled** (aborts outer traces) and leaking callbacks without explicit `:free()` exhausts the fixed trampoline pool with a fatal runtime error.

---

### 3. PHP Zend Engine (8.x): 16-Byte `zval`, Copy-on-Write Containers, and `IS_REFERENCE` Splitting Semantics

#### 3.1 `zval`, `zend_reference`, and Dual-Mode `HashTable` Layout

Basis: source

Since PHP 7.0 (inspected in `php/php-src` 8.7.0-dev, `Zend/zend_types.h:321-462, 632-678, 755-790`), Zend eliminated heap allocation of individual scalar wrappers by embedding `zval` directly by value inside VM call frames, object property tables, and array buckets:

```c
/* php/php-src Zend/zend_types.h:341-360 (16 bytes on 64-bit) */
struct _zval_struct {
    zend_value        value;          /* 8-byte union: lval, dval, *counted, *str, *arr, *obj, *ref, *zv */
    union {
        uint32_t type_info;
        struct { uint8_t type; uint8_t type_flags; uint16_t extra; } v;
    } u1;                             /* 4 bytes: active type tag + IS_TYPE_REFCOUNTED + flags */
    union {
        uint32_t next;                /* hash collision chain (in Bucket) */
        uint32_t cache_slot;          /* inline cache / RECV_INIT slot */
        uint32_t opline_num;          /* FAST_CALL opline */
        uint32_t num_args;            /* arg count on EX(This) */
        ...
    } u2;                             /* 4 bytes: context-dependent auxiliary metadata */
};
```

Key representation invariants:

1. **Immediate vs. refcounted types (`zend_types.h:644-670`)**: `IS_UNDEF` (0), `IS_NULL` (1), `IS_FALSE` (2), `IS_TRUE` (3), `IS_LONG` (4), and `IS_DOUBLE` (5) are pure value types with zero heap allocation and no reference count. `IS_STRING` (6), `IS_ARRAY` (7), `IS_OBJECT` (8), `IS_RESOURCE` (9), `IS_REFERENCE` (10), and `IS_CONSTANT_AST` (11) point to heap structs beginning with `zend_refcounted_h gc` (`uint32_t refcount` + `uint32_t type_info`).
2. **GC flags (`zend_types.h:755-765`)**: `GC_IMMUTABLE` (`1<<6`) marks interned strings and opcache-shared constant arrays that cannot be mutated or refcounted in place; `GC_PERSISTENT` (`1<<7`) marks `malloc`-allocated cross-request data (reused on `IS_OBJECT` as `WEAKLY_REFERENCED`, `zend_types.h:1503-1505`); `GC_PROTECTED` (`1<<5`) detects recursive traversal.
3. **Reference wrapper (`zend_types.h:632-636`)**: PHP references (`$b = &$a`) are represented by a dedicated heap box:
   ```c
   struct _zend_reference {
       zend_refcounted_h              gc;
       zval                           val;     /* inner wrapped value */
       zend_property_info_source_list sources; /* typed properties bound to this reference */
   };
   ```
   The `sources` list enforces PHP 7.4+ typed-property invariants: whenever any alias writes through a `zend_reference` that is bound to one or more typed object properties (`public int $x`), Zend checks/coerces the assigned value against every property type in `sources`.
4. **Packed vs. Associative `HashTable` (`zend_types.h:400-465`)**: PHP's `zend_array` (`HashTable`) is an insertion-ordered map with two memory layouts sharing one header:
   - **Packed arrays** (`HT_IS_PACKED(ht)`): `arPacked` points to a contiguous array of 16-byte `zval`s (`HT_MIN_SIZE = 8`, max `0x40000000` on 64-bit) with a minimal 2-slot `HT_INVALID_IDX` negative header, halving memory overhead compared to full buckets.
   - **Hash arrays**: `arData` points to an array of 32-byte `Bucket`s (`zval val` + `zend_ulong h` + `zend_string *key`), while negative indices `((uint32_t*)ht->arHash)[(int32_t)(h | ht->nTableMask)]` store the hash lookup table directly *before* `arData` in a single allocation, chaining collisions through `Bucket.val.u2.next`!

#### 3.2 Copy-on-Write vs. `$a = &$b` Reference Splitting State Machine

Basis: source + execution (executable state-machine model)

Zend's value vs. reference assignment transitions (`Zend/zend_types.h:1475-1610`, `Zend/zend_vm_def.h:9399-9430`) follow four exact rules:

1. **Value copy (`$b = $a`)**: Executes `ZVAL_COPY_DEREF` (`zend_types.h:1547-1560`).
   - If `$a` is a non-refcounted scalar, its 16-byte `zval` is copied bitwise.
   - If `$a` is a refcounted non-reference (e.g., `IS_ARRAY` with `refcount = 1`), `$b` copies the pointer and increments `Z_ADDREF_P($a)` (`refcount` becomes `2`). No array duplication occurs yet (lazy CoW).
   - If `$a` is `IS_REFERENCE` (pointing to `zend_reference *r`), `ZVAL_COPY_DEREF` **dereferences** to `&r->val`, increments the inner value's refcount (if refcounted), and stores a **non-reference** copy in `$b`! Thus `$b = $a` never propagates top-level reference status.
2. **Copy-on-Write mutation (`$b[0] = 99`)**: Before mutating an array in place, Zend invokes `SEPARATE_ARRAY(zv)` (`zend_types.h:1575-1582`):
   ```c
   if (UNEXPECTED(GC_REFCOUNT(_arr) > 1)) {
       ZVAL_ARR(__zv, zend_array_dup(_arr));
       GC_TRY_DELREF(_arr);
   }
   ```
   (Immutable opcache arrays carry `GC_IMMUTABLE` and `GC_REFCOUNT == 2` / non-refcounted type flags so they always separate on write without touching shared-memory refcounts.)
3. **Reference binding (`$b = &$a`)**: Executes `ZEND_MAKE_REF` (`zend_vm_def.h:9399-9430`) / `ZVAL_MAKE_REF_EX(op1, 2)`:
   - If `$a` is not yet `IS_REFERENCE`, Zend allocates a new `zend_reference` with `gc.refcount = 2`, moves `$a`'s `zval` payload into `ref->val` (preserving any underlying array's `refcount`!), overwrites `$a` with `IS_REFERENCE -> ref`, and sets `$b` to `IS_REFERENCE -> ref`.
   - If `$a` already shared an array via CoW (`$x = [1, 2]; $a = $x; $b = &$a;`), note that `ref->val` still points to the shared `zend_array` (`refcount = 2`) — the array is **not** eagerly copied when taking a reference; instead, a subsequent write to `$b[0]` triggers `SEPARATE_ARRAY(&ref->val)`, updating `ref->val` in place so `$a` and `$b` see the newly separated array while `$x` retains the original!
4. **Forced un-referencing (`SEPARATE_ZVAL`, `zend_types.h:1592-1610`)**: Used when an operation requires an unshared non-reference value. If `Z_ISREF_P(zv)`: copies `r->val` out, decrements `r`'s refcount (freeing `r` if `0`), and if `r` is still shared (`rc > 0`) and `r->val` is `IS_ARRAY`, eagerly duplicates the array via `zend_array_dup`.

#### 3.3 The Nested Array `IS_REFERENCE` Persistence Hazard

Basis: source + execution (executable state-machine model)

A critical asymmetry between PHP's outer value semantics and inner reference slots resides directly in `zend_array_dup_value` (`Zend/zend_hash.c:2546-2560`), called by `zend_array_dup` during every `SEPARATE_ARRAY`:

```c
/* php/php-src Zend/zend_hash.c:2546-2560 */
do {
    if (Z_OPT_REFCOUNTED_P(data)) {
        if (Z_ISREF_P(data) && Z_REFCOUNT_P(data) == 1 &&
            (Z_TYPE_P(Z_REFVAL_P(data)) != IS_ARRAY ||
              Z_ARRVAL_P(Z_REFVAL_P(data)) != source)) {
            data = Z_REFVAL_P(data);
            if (!Z_OPT_REFCOUNTED_P(data)) {
                break;
            }
        }
        Z_ADDREF_P(data);
    }
} while (0);
ZVAL_COPY_VALUE(dest, data);
```

This 15-line block yields three sharp, non-obvious behavioral regimes verified by our executable state-machine model:

1. **Active inner reference (`refcount > 1`) leaks aliasing across CoW copies**:
   In `$a = [10, 20]; $r = &$a[0]; $c = $a; $c[0] = 99;`:
   - `$r = &$a[0]` wraps element `0` inside a `zend_reference` with `refcount = 2` (referenced by `$a[0]` and `$r`).
   - `$c = $a` increments `$a`'s `HashTable` refcount to `2` (CoW shared).
   - `$c[0] = 99` calls `SEPARATE_ARRAY($c)` -> `zend_array_dup($a)`. Because `$a[0]` is `IS_REFERENCE` with `refcount == 2 != 1`, `zend_array_dup_value` skips unwrapping, calls `Z_ADDREF_P(data)` (`refcount` becomes `3`), and copies the `IS_REFERENCE` pointer directly into `$c[0]`.
   - Writing `99` to `$c[0]` writes through the shared `zend_reference`, **mutating `$a[0]` and `$r` to `99` even though `$a` and `$c` are distinct `HashTable`s**!
   - This is the root mechanism behind PHP's notorious `foreach ($arr as &$v) {}` bug: if `$v` is not `unset($v)` after the loop, the last element remains `IS_REFERENCE` (`refcount = 2`), silently corrupting future CoW copies of `$arr` or subsequent `foreach ($arr as $v)` loops.
2. **Orphaned inner reference (`refcount == 1`) is lazily unwrapped on CoW duplication**:
   If `unset($r)` executes *before* `$c[0] = 99`, `$a[0]` remains `IS_REFERENCE` with `refcount = 1`. When `$c[0] = 99` invokes `zend_array_dup`, `Z_REFCOUNT_P(data) == 1` holds, so Zend unwraps `data = Z_REFVAL_P(data)` into `$c[0]`, restoring full value isolation (`$a[0] == 10`, `$c[0] == 99`).
3. **Self-referential array cycles are intentionally preserved (`Z_ARRVAL_P(Z_REFVAL_P(data)) == source`)**:
   If `$a[0] = &$a;` (`refcount == 1` on the wrapper or recursive copy), unwrapping would lose the cycle identity; Zend suppresses unwrapping when the inner value points directly to `source`.

Additionally, `zend_array_dup_ht_iterators` (`Zend/zend_hash.c:2587-2603`) must clone active `EG(ht_iterators)` entries onto duplicated arrays so that mutations during `foreach` preserve PHP's snapshot-like iteration semantics without dangling pointers.

---

### 4. GNU R and the RIR/PIR JIT Compiler: Call-by-Need `PROMSXP` Promises, Non-Standard Evaluation, and Speculative Environment Elision

#### 4.1 `SEXPREC` and `PROMSXP` Call-by-Need Implementation

Basis: source + documentation

Every runtime value in GNU R (`wch/r-source`, `src/include/Defn.h:184-243`, `src/include/Rinternals.h`) is a heap-allocated `SEXPREC` (7 machine words = 56 bytes on 64-bit) or `VECTOR_SEXPREC` (6 words = 48 bytes header followed by inline vector elements), starting with `SEXPREC_HEADER` (`sxpinfo_struct`, `attrib`, generational GC `gengc_next_node`/`gengc_prev_node`).

Unlike call-by-value scripting languages, R binds every argument in a closure call (`applyClosure` / `matchArgs_NR`) as a **call-by-need promise** (`PROMSXP`, `Defn.h:184-188`):

```c
/* wch/r-source src/include/Defn.h:184-188 */
struct promsxp_struct {
    struct SEXPREC *value;  /* R_UnboundValue while unevaluated; cached result once forced */
    struct SEXPREC *expr;   /* unevaluated AST (SEXP) captured at the call site */
    struct SEXPREC *env;    /* lexical environment (ENVSXP) in which expr will be evaluated; R_NilValue once forced */
};
```

When a symbol bound to a `PROMSXP` is first read, `eval()` invokes `forcePromise(SEXP e)` (`src/main/eval.c:954-989`), executing a strict 6-step protocol:

1. **Memoization check**: If `PROMISE_IS_EVALUATED(e)` (`PRVALUE(e) != R_UnboundValue`), return the cached value immediately without re-evaluating `PRCODE(e)`.
2. **Recursion-cycle and restart detection (`PRSEEN`)**:
   - `PRSEEN(e) == 1`: raises an error (`"promise already under evaluation: recursive default argument reference or earlier problems?"`).
   - `PRSEEN(e) == 2`: occurs when a previous evaluation of `e` was aborted via `longjmp` (e.g., an error or user interrupt caught by `tryCatch` while `e` was on the pending-promise stack `RPRSTACK`); sets `PRSEEN(e) = 1` and emits `"restarting interrupted promise evaluation"`.
3. **Pending-stack registration**: Sets `PRSEEN(e) = 1` and links `e` onto the C-stack `RPRSTACK` (`PUSH_PENDING_PROMISE(e, &prstack)`) so non-local jumps unwind and mark `PRSEEN = 2` rather than leaving the promise permanently poisoned at `1`.
4. **Evaluation**: Evaluates `val = eval(PRCODE(e), PRENV(e))` in the *caller's* environment (or the callee's environment for default argument expressions!).
5. **Memoization & sharing escalation**: Stores `SET_PRVALUE(e, val)` and calls `ENSURE_NAMEDMAX(val)` (preventing subsequent callers from mutating the cached promise value in place without copying).
6. **Environment release**: Pops `RPRSTACK`, resets `PRSEEN(e) = 0`, and sets **`SET_PRENV(e, R_NilValue)`** so the GC can collect the caller's environment once no unevaluated promises reference it (`eval.c:980-986`). Notice, however, that **`PRCODE(e)` is NOT cleared** — `substitute()` can still inspect the original AST even *after* the promise has been forced!

#### 4.2 Non-Standard Evaluation (`substitute()`, `parent.frame()`) and First-Class Mutable Environments

Basis: source + documentation (peer-reviewed empirical literature)

Goel & Vitek (PACMPL OOPSLA 2019, `10.1145/3360579`, studying 16,707 CRAN/Bioconductor packages and >270 billion promises) demonstrated empirically that R code almost never uses call-by-need for Haskell-style infinite data structures or avoiding dead work; instead, laziness is overwhelmingly exploited for **non-standard evaluation (NSE)** and metaprogramming (`dplyr`, `ggplot2`, `subset`, `lm` formulas):

- **`substitute(expr, env)` (`src/main/coerce.c:2843-2927`)**: `do_substitute` is a `SPECIALSXP` that receives its arguments *unevaluated*. Walking the AST via `substituteList(t, env)` (defaulting `env = rho`, the current closure frame, except when `env == R_GlobalEnv` where substitution is suppressed for historical reasons, `coerce.c:2913-2914`), whenever `substitute` encounters a symbol bound to a `PROMSXP` in `env`, it substitutes **`PRCODE(p)`** (the captured source AST) **without forcing the promise**!
- **`parent.frame(n)` and `RCNTXT` (`src/include/Defn.h:1415-1435`, `src/main/envir.c`)**: Every closure invocation pushes an `RCNTXT` evaluation context onto R's C stack (`R_GlobalContext`), recording `cloenv` (the callee's `ENVSXP`), `sysparent` (the caller's `ENVSXP`), `promargs` (the call's promise list), `call` (the call AST), and `cjmpbuf` (`setjmp`/`longjmp` target). Builtins like `parent.frame(n)`, `sys.frame()`, `sys.call()`, `match.call()`, and `eval(..., parent.frame())` traverse this dynamic `RCNTXT` chain and obtain **live mutable handles** to ancestor frames.
- **Semantic consequence for compilers and verifiers**: Because (a) forcing a promise executes arbitrary side effects in another environment (`<<-`, `assign(..., envir = parent.frame())`), (b) evaluating arguments in a different order changes observable side effects, and (c) *any* unknown callee can reflectively read or mutate local variables in its caller's frame via `parent.frame()`, standard lexical scoping, dead-store elimination, constant propagation, and eager argument evaluation are **globally unsound** in unguarded R code (Morandat et al., ECOOP 2012, `10.1007/978-3-642-31057-7_6`).

#### 4.3 RIR/PIR JIT Compilation: Contextual Dispatch, Force Dominance, and Speculative Environment Elision

Basis: source + documentation (peer-reviewed papers)

The **Ř / RIR** compiler (`reactorlabs/rir`, Flückiger et al. DLS 2019 `10.1145/3359619.3359744` & OOPSLA 2020 `10.1145/3428288`) bridges R's hostile semantics and optimizing JIT compilation using a two-tier IR (bytecode `RIR` + SSA `PIR` with explicit `MkEnv`, `MkArg`, `Force`, `LdVar`, `StVar`, `PushContext`, and `Checkpoint`/`Deopt` instructions):

1. **Contextual Dispatch (`rir/src/runtime/Context.h:13-66`)**: Rather than compiling one monolithic version of a closure, RIR specializes functions on a bitset of **caller-guaranteed assumptions** (`Context`):
   - `TypeAssumption`: per-argument bits for the first 6 arguments (`Arg0..5IsEager_` — argument already evaluated, no `PROMSXP` needed; `Arg0..5IsNonRefl_` — forcing cannot reflect on caller environments; `Arg0..5IsNotObj_` — not an S3/S4 object, bypassing generic dispatch; `Arg0..5IsSimpleInt_` / `Arg0..5IsSimpleReal_`).
   - `Assumption`: call-shape invariants (`NoExplicitlyMissingArgs`, `CorrectOrderOfArguments`, `NotTooManyArguments`, `StaticallyArgmatched`).
   Call sites dispatch to the most specialized compiled `ClosureVersion` whose required `Context` is a subset of the caller's provided `Context`, eliminating millions of `PROMSXP` allocations on hot paths while falling back seamlessly when a caller passes a lazy or reflective argument.
2. **Staged Optimization Pipeline (`rir/src/compiler/opt/pass_scheduler.cpp:39-95`)**:
   - The **`Initial` stage** performs sound static optimizations: `EagerCalls` -> `MatchCallArgs` -> `InlineForcePromises` -> `Inline` -> `ForceDominance` -> `ScopeResolution` -> `LoadElision` -> `GVN` -> `ElideEnv` -> `DelayEnv`.
   - `ForceDominance` (`rir/src/compiler/opt/force_dominance.cpp:18-65`) proves when a promise `MkArg(exp)` is guaranteed to be forced before any intervening effect, inlines `eval(exp)` to compute `f'`, and — if the enclosing environment `e = MkEnv(x=a)` escaped (e.g., to a `PushContext` for `substitute()`/`promargs`) — synthesizes an already-evaluated `a' = MkArg(exp, f')` and emits `StVar(x=a', e)` so `substitute()` still sees `exp` while readers use `f'` directly! Crucially (`force_dominance.cpp:51-65`), it refuses to depromise `MissingArg::instance()` because promised vs. depromised missing arguments behave differently under R's `missing()`.
   - `ElideEnv` (`rir/src/compiler/opt/elide_env.cpp:60-90`) distinguishes instructions that require a materialized `ENVSXP` (`envNeeded`) from instructions whose `EnvStubInfo` permits a lazy stack-resident environment stub (`envStubNeeded`, materialized only on deoptimization).
3. **Speculative Environment Elision (`ElideEnvSpec`, `rir/src/compiler/opt/elide_env_spec.cpp:33-70`)**: In the **`Speculation` stage**, for primitives in `SafeBuiltinsList::nonObject(...)` that only inspect environments when dispatched to S3/S4 methods on `OBJECT(x) == 1` values, `ElideEnvSpec` inserts a guard against an available `Checkpoint` verifying that observed arguments are non-objects (`!arg->type.maybeObj()`), elides the `MkEnv` dependency entirely, and deoptimizes back to RIR bytecode (reconstructing the `ENVSXP` and `RCNTXT` lazily from the checkpoint frame) if an S3/S4 object or reflective builtin ever appears.

#### 4.4 GNU R Memory Management (`REFCNT` and `PROTECT` Stack) at the C FFI Boundary

Basis: source

- **Reference-counting CoW (`Defn.h:194-196, 234`, `eval.c:993-1022`)**: Modern GNU R replaces the legacy 2-bit `NAMED` saturating counter (`0/1/2`) with `SWITCH_TO_REFCNT` (`REFCNTMAX = (1 << NAMED_BITS) - 1`), exposing `MAYBE_SHARED(x)` (`REFCNT(x) > 1`) to decide when mutating primitives must duplicate a vector. To avoid per-push refcount traffic in functional bytecode, the bytecode engine defers incrementing stack link counts until a potentially mutating operation calls `INCLNK_stack_commit()` (`eval.c:1012-1022`).
- **C FFI `.Call` pointer-protection hazard (`Rinternals.h`)**: R's garbage collector is **precise and non-conservative** with respect to the C stack — it cannot discover `SEXP` local variables in C registers or stack frames. Every C function called via `.Call` must push newly allocated `SEXP`s onto R's auxiliary `R_PPStack` via `PROTECT(s)` before calling *any* R API function that might allocate (and therefore trigger GC), and balance every push with `UNPROTECT(n)` before returning (matching `RCNTXT.cstacktop` unwinding on `Rf_error()`). Missing a single `PROTECT` across an allocating call creates silent, allocation-timing-dependent use-after-free bugs (`rchk` static analysis is specifically built to detect these).

---

### 5. Perl 5: Context-Sensitive `wantarray` Dispatch, Multi-Slot `SV` Representation, and Re-Entrant `tie` Magic

#### 5.1 Multi-Slot `SV` Representation, Monotone Upgrading, and Dualvars

Basis: source + execution (Perl 5.40.1 `Devel::Peek`)

In Perl 5 (`Perl/perl5`, `sv.h:246-290, 418-515`), every value is a heap-allocated `struct sv` head containing `sv_any` (pointer to an optional typed body `XPV*`), `sv_refcnt` (reference count), `sv_flags` (low 8 bits `SVTYPEMASK = 0xff` encoding `svtype`, upper 24 bits holding validity, magic, and ownership flags), and an inline `SV_HEAD_UNION_` (`svu_iv`, `svu_uv`, `svu_rv`, `svu_pv`, etc.):

- **Monotone `SvUPGRADE` (`sv.h:428-429`)**: Scalars start minimal (`SVt_NULL`, `SVt_IV`, `SVt_PV`) and upgrade monotonically in place via `sv_upgrade(sv, mt)` (e.g., to `SVt_PVNV` when storing both string and float, or `SVt_PVMG` when attaching `MAGIC` or blessing an object) without changing the `SV*` pointer address.
- **Independent multi-representation flags (`sv.h:431-460`)**: Public validity bits `SVf_IOK` (`0x100`), `SVf_NOK` (`0x200`), `SVf_POK` (`0x400`), and `SVf_ROK` (`0x800`), paired with private cached bits `SVp_IOK`/`SVp_NOK`/`SVp_POK`, are **not mutually exclusive** (except `SVf_ROK` vs numeric `SVp_*`, `sv.h:534`). A single `SV` can simultaneously carry a valid integer (`IV`) and an unrelated string (`PV`) — known as a **dualvar** (used by core `$!` / `Errno`, and constructed via `Scalar::Util::dualvar`). Live `Devel::Peek::Dump` on Perl 5.40.1 for `dualvar(42, "forty-two")` confirms:
  ```text
  SV = PVNV(...)
    REFCNT = 1
    FLAGS = (IOK,POK,IsCOW,pIOK,pPOK)
    IV = 42
    PV = ... "forty-two"\0  CUR = 9  LEN = 16  COW_REFCNT = 1
  ```
  Consequently, serializers (JSON/CBOR/RPC) and FFI bridges inspecting a Perl `SV` cannot determine a unique "runtime type" without imposing a precedence rule (e.g., testing `SvROK` -> `SvIOK`/`SvNOK` -> `SvPOK`), and inspecting a scalar in numeric context (`$x + 0`) can silently set `SVp_IOK`/`SVf_IOK` and alter how subsequent JSON encoders serialize `$x` (a well-known Perl JSON typing bug).
- **Readonly split (`sv.h:444-452`)**: Perl distinguishes user-toggleable `SVf_READONLY` (e.g., `Hash::Util::lock_hash`) from core immutability `SVf_READONLY | SVf_PROTECT`, and combines mutation guards into `SVf_THINKFIRST` (`SVf_READONLY|SVf_PROTECT|SVf_ROK|SVf_FAKE|...`, `sv.h:491`).

#### 5.2 Tri-State Call Context (`OPf_WANT_*` / `GIMME_V` / `wantarray`) and List-Context Injection

Basis: source + execution (Perl 5.40.1)

Every Perl expression and subroutine invocation carries a **tri-state syntactic context** resolved at compile time into the 2-bit `OPf_WANT` mask (`op.h:108-111`): `OPf_WANT_VOID = 1` (`G_VOID`), `OPf_WANT_SCALAR = 2` (`G_SCALAR`), and `OPf_WANT_LIST = 3` (`G_LIST`, historically `G_ARRAY`), or `0` (inherited dynamically from the caller's `PERL_CONTEXT.blk_gimme`). At runtime, `pp_wantarray` (`pp_ctl.c:45-78`) walks the context stack (`dopopto_cursub()`) and returns:
- `&PL_sv_yes` (`1`, true) for `G_LIST`,
- `&PL_sv_no` (`""`, defined false) for `G_SCALAR`,
- `&PL_sv_undef` (`undef`) for `G_VOID` (or outside a subroutine).

Because context propagates into function calls inside list expressions — crucially including **hash constructors** `my %h = (key1 => expr1, key2 => expr2)` where `=>` is merely a comma operator — any callee inside a hash literal runs in **list context (`G_LIST`)**! Live execution on Perl 5.40.1 verifies the classic **Perl hash-constructor parameter-injection vulnerability**:

```perl
sub odd_list { return wantarray ? ('a', 'role', 'admin') : 'safe'; }
my %overwritten = (role => 'guest', x => odd_list());
# Live Perl 5.40.1 output:
#   overwritten: role=admin, x=a
```

When an unguarded callee (such as CGI's historical `$q->param('x')`) returns 0 elements or >1 elements in list context inside `(role => 'guest', x => f())`, the flat argument list shifts keys and values, allowing attacker-controlled input to inject arbitrary hash keys and overwrite security-critical entries (`role => 'admin'`). Defensive Perl requires forcing scalar context (`x => scalar(f())`).

#### 5.3 `MAGIC` Linked Lists, `tie` Vtables, and Re-Entrant Callback Hazards

Basis: source + execution (Perl 5.40.1)

Perl implements virtualized variables (`tie`), taint tracking, regex `$1`, `%ENV`, and overloading through a singly linked list of `struct magic` nodes (`mg.h:23-32`) attached to `SVt_PVMG` (or higher) scalars, arrays, and hashes, gated by three flag bits in `sv_flags` (`sv.h:458-460`):
- `SVs_GMG` (`0x00200000`): has get-magic (`Perl_mg_get`, `mg.c:616-651`)
- `SVs_SMG` (`0x00400000`): has set-magic (`Perl_mg_set`, `mg.c:734-769`)
- `SVs_RMG` (`0x00800000`): has random magic (clear, length, copy, local, etc.)

In Perl 5.45.5 (`blead`), `mg.h:35` and `mg.c:639-650, 757-764` additionally introduce **`MGf_MGv2` (`0x80`)**, dispatching to structured v2 scalar-variable (`MGv2s_SCALARVAR`: `pre_get`/`post_set`) and value-magic (`MGv2s_SCALARVALUE`, `SVs_VMG`) function tables alongside classic v1 `MGVTBL` vtables.

For `tie` (`mg.c:2968-3015`), tying a scalar attaches a `MAGIC` node with `mg_type = PERL_MAGIC_tiedscalar` (`'q'`) and `mg_virtual = &PL_vtbl_packelem` (verified directly in our live Perl 5.40.1 `Devel::Peek::Dump` output: `FLAGS = (GMG,SMG,RMG,IOK,pIOK)`, `MG_VIRTUAL = &PL_vtbl_packelem`, `MG_TYPE = PERL_MAGIC_tiedscalar(q)`, `MG_OBJ = CounterTie`). Tying a hash or array attaches `PERL_MAGIC_tied` (`'P'`), while indexing an element produces a temporary `PVLV` proxy carrying `PERL_MAGIC_tiedelem` (`'p'`). Key operational subtleties:

1. **Re-entrancy suppression (`save_magic_flags`)**: `Perl_mg_get` and `Perl_mg_set` (`mg.c:620-650, 738-769`) snapshot and temporarily clear `SVs_GMG`/`SVs_SMG` on the save stack (`MGS`) while invoking `svt_get`/`svt_set`, preventing infinite recursion if the magic handler reads/writes the underlying SV, and explicitly cache `nextmg = mg->mg_moremagic` before each callback because `svt_get()` may delete itself, prepend new magic, or upgrade the SV (`mg.c:628-637`).
2. **`MGf_GSKIP` element caching (`mg.c:2972-2973, 749-752`)**: `Perl_magic_getpack` sets `MGf_GSKIP` on `PERL_MAGIC_tiedelem` (`'p'`) proxies (so multiple internal fetches of a single element proxy don't re-invoke `FETCH` until the next `mg_set` clears `MGf_GSKIP`), whereas **`PERL_MAGIC_tiedscalar` (`'q'`) does NOT set `MGf_GSKIP`**, so every single read fires `FETCH`!
3. **Arbitrary side-effects inside pure expressions (live execution on Perl 5.40.1)**: Running `my $sum1 = $x + $y;` where `$x` is tied to `CounterTie` (initial `5`, whose first `FETCH` increments `$y` from `10` to `110`) yields **`sum1 = 115`** (left-to-right operand evaluation fires `$x`'s `FETCH` before `$y` is read), and calling `defined($x)` fires a 3rd `FETCH` (`fetches = 3, stores = 1`) — even predicates that look purely structural trigger arbitrary user Perl code!

#### 5.4 XS / C-API Stack Reallocation Hazard Under Re-Entrant Magic

Basis: source + derived

In Perl's C extension API (`XSUB.h:158-175`), an XSUB begins with `dXSARGS` (`dSP; dAXMARK; dITEMS`), which caches a local C pointer `SV **sp = PL_stack_sp` into Perl's heap-allocated argument stack (`PL_stack_base`). Because Perl's argument stack grows dynamically via `realloc` whenever Perl code pushes frames, **calling almost any scalar accessor (`SvPV`, `SvIV`, `SvNV`) on a `SVs_GMG` tied argument invokes `Perl_mg_get` -> `magic_methcall1` -> arbitrary Perl `FETCH()` -> potential `PL_stack_base` reallocation**!

If an XS function (1) caches `SV *arg = ST(0)` or pushes results onto `sp` without bracketing re-entrant magic calls with `PUTBACK; ...; SPAGAIN;`, or (2) holds raw `char *pv = SvPV(ST(0), len)` across reading `ST(1)` (whose `FETCH` may mutate `ST(0)` and free its `PV` buffer!), the C code dereferences a dangling `PL_stack_base` or freed string buffer. Sound XS / FFI bindings must evaluate get-magic up front (`SvGETMAGIC`), copy or snapshot buffers before touching subsequent arguments, and re-synchronize `SPAGAIN` around every call capable of re-entering Perl.

---

### 6. Synthesis for Verification, Compiler Analysis, and FFI Bridge Design

Basis: derived (synthesized from Sections 2–5)

Across these four runtime families, four recurring boundary invariants govern safe compiler optimization, static analysis, and FFI/verification bridges:

1. **Canonicalization at untyped-to-tagged FFI boundaries**: Any NaN-boxed runtime (`LuaJIT/LuaJIT`) must enforce bit-level float canonicalization on every C-to-VM numeric read, or explicitly mark FFI-read `double`s as a trusted-code invariant; tagged-union layouts (`lua/lua` 5.5, `php/php-src`) pay higher register/slot footprint to eliminate this entire attack surface.
2. **Deep vs. shallow copy-on-write isolation**: CoW refcounting (`php/php-src` `SEPARATE_ARRAY`, `wch/r-source` `MAYBE_SHARED`) guarantees structural isolation only when container elements cannot carry shared indirection cells (`IS_REFERENCE` in PHP, `ENVSXP` in R). Any alias analysis or verifier assuming value semantics for PHP arrays must track whether any descendant bucket can contain an `IS_REFERENCE` with `refcount > 1`.
3. **Materialization of lazy/reflective runtime state on deoptimization**: Both LuaJIT (`RID_SINK` -> `snap_unsink`) and RIR/PIR (`MkEnv`/`MkArg` -> `Checkpoint`/`Deopt`) show that optimizing dynamic runtimes requires maintaining an exact **reconstruction map** from scalarized/elided JIT state back to the interpreter's reified heap objects (`GCtab`/`GCcdata` in LuaJIT, `ENVSXP`/`PROMSXP`/`RCNTXT` in R) at every potentially observable exit point.
4. **Re-entrancy across implicit read/coercion hooks**: Metatables (Lua/LuaJIT), lazy promises (R), and `MAGIC`/`tie` (Perl) turn syntactically pure expressions (`t[k]`, `x + y`, `defined($x)`, `SvPV(sv)`) into arbitrary user-code invocations capable of mutating sibling variables, invalidating negative caches, triggering GC, or reallocating C-API stacks. FFI wrappers must enforce snapshot-before-coerce ordering and GC/stack re-rooting around every potentially hookable access.

## Boundaries

- **PHP 8 OPcache JIT (`ext/opcache/jit`)**: `not examined`. This report covers Zend VM `zval` / `HashTable` / `IS_REFERENCE` / CoW semantics in `Zend/`, not PHP 8's DynASM/IR tracing and function JIT code generation or its deoptimization triggers.
- **LuaJIT non-`LJ_GC64` / 32-bit architectures and ARM64/MIPS/PPC backends**: `not examined` beyond the `!LJ_GC64` `TValue` tag encoding in `src/lj_obj.h` and callback head constants in `src/lj_ccallback.c`. Exact register allocation and machine-code exit stub encodings are architecture-specific.
- **LuaJIT trace compilation of C-to-Lua FFI callbacks**: `unsupported` by LuaJIT (`lj_ccallback.c`); C-to-Lua callback re-entry always aborts outer trace recording and runs via bounded machine-code trampoline slots.
- **GNU R ALTREP, S4/R6 dispatch, and byte-compiler (`compiler` package) internals**: `not examined`. The analysis focuses on core `SEXPREC`/`PROMSXP`, `forcePromise`, `substitute`, `parent.frame`, `REFCNT`/`PROTECT`, and RIR/PIR's compilation model.
- **Perl 5.45 `MGf_MGv2` (`MGv2s_SCALARVAR` / `MGv2s_SCALARVALUE`) public XS API stability**: `unknown`. Observed directly in `Perl/perl5` `blead` 5.45.5 (`mg.h:35`, `mg.c:639-650, 757-764`), which is an active development branch; whether its exact v2 struct ABI will freeze unchanged in Perl 5.46 is not resolved by source inspection alone.
- **Execution of LuaJIT, PHP, and GNU R/RIR binaries**: `not examined` via live interpreter execution in this environment (those binaries were not installed on the observation host; only Perl 5.40.1 was executed live). Bit-level LuaJIT `LJ_GC64` NaN-boxing and PHP `zend_array_dup_value` CoW/reference transitions were verified via Python executable models faithfully transcribed from the pinned C sources, which check the modeled C expressions but cannot catch discrepancies introduced by platform-specific C compilers or unmodeled VM opcodes.
- **Generalization to Lua 5.1–5.4**: `known not to apply` for Lua 5.5's 9-byte split-array `Table.array` layout (`ltable.h:95-125`), which is new in Lua 5.5 (earlier versions stored `TValue *array` at 16 bytes/slot on 64-bit).

## Evidence

### Pinned Upstream Source Inspections (Observed 2026-11-19)

1. **`lua/lua` (`c42d820bc0c3bc4f2ad536e19d2f05405af10387`, Lua 5.5.1)**:
   - `lua.h:20-25, 515-520`: version `5.5.1`.
   - `lobject.h:49-78`: `union Value`, `struct TValue`, `TValuefields`.
   - `lobject.h:752-786`: `union Node` (24-byte key/value packed node) and `struct Table` (`Value *array`, `lu_byte flags`).
   - `ltable.h:18-165`: `invalidateTMcache`, `BITDUMMY`, `luaH_fastgeti`/`luaH_fastseti`, bidirectional split array (`getArrTag`, `getArrVal`, `lenhint`).
   - `ltm.h:19-68` and `ltm.c:50-100`: `TMS` enum (`TM_INDEX..TM_EQ`, `TM_CLOSE`), `maskflags`, `luaT_gettm` negative-cache bit update, `luaT_gettmbyobj`.
2. **`LuaJIT/LuaJIT` (`63c8f1a9b479ba5518cf6a170ff7729178bc3cfd`, branch `v2.1`, `LuaJIT 2.1.ROLLING`)**:
   - `src/luajit_rolling.h:33-37`: version `LuaJIT 2.1.ROLLING`.
   - `src/lj_obj.h:70-77, 174-298, 348-365, 616-618, 783-813, 948-957`: `TValue` NaN-boxing (`!LJ_GC64` and `LJ_GC64`), `setgcreft`, `LJ_TNIL..LJ_TNUMX`, `LJ_TISNUM`, `LJ_GCVMASK`, `LJ_LIGHTUD_BITS_SEG=8` / `LJ_LIGHTUD_BITS_LO=39`, `itype(o)`, `tvisnum(o)`, `setnanV(o)`, `GCcdata`, `GCcdataVar`.
   - `src/lj_cconv.c:380-423`: `lj_cconv_tv_ct` lines 396–400 confirming no release-build NaN canonicalization (`lj_assertCTS(tvisnum(o), "non-canonical NaN passed")`).
   - `src/lj_jit.h:217-313`: `snap_pc`, `TraceLink`, `GCtrace`, `HotPenalty` (`PENALTY_SLOTS=64`, `PENALTY_MIN=72`, `PENALTY_MAX=60000`).
   - `src/lj_opt_sink.c:1-90` and `src/lj_snap.c:860-965`: `RID_SINK` allocation sinking, `snap_unsink` (`GCcdata` `IR_XSTORE` and `GCtab` `IR_TNEW`/`IR_TDUP`/`IRFL_TAB_META` materialization), `lj_snap_restore`.
   - `src/lj_traceerr.h:9-40`: NYI abort reasons (`NYIBC`, `NYIFFU`, `NYIRETL`, `NYITMIX`, `NYICONV`, `NYICALL`).
   - `src/lj_meta.c:57-520`: `nomm` negative cache set and invalidation (`t->nomm = 0`), `lj_meta_lookup` including `tviscdata`.
   - `src/lj_cdata.h:27-75`, `src/lj_crecord.c:1123-1350`, `src/lj_ccallback.c:26-80`: `GCcdata` constructors, `crec_call` -> `IR_CALLXS`, `CALLBACK_MCODE_SIZE`/`CALLBACK_MAX_SLOT`.
3. **`php/php-src` (`e709ba4099085a5ee6a15846c32110873a15474a`, PHP `8.7.0-dev`)**:
   - `main/php_version.h:3-8`: version `8.7.0-dev`.
   - `Zend/zend_types.h:321-360, 400-508, 632-678, 755-790, 1478-1610`: `zend_value`, `_zval_struct`, `HashTable` (`arHash`/`arData`/`arPacked`), `_zend_reference` (`gc`, `val`, `sources`), `IS_*` tags, `GC_IMMUTABLE`/`GC_PERSISTENT`/`GC_PROTECTED`, `ZVAL_COPY_OR_DUP`, `ZVAL_MAKE_REF`, `ZVAL_UNREF`, `ZVAL_COPY_DEREF`, `SEPARATE_STRING`, `SEPARATE_ARRAY`, `SEPARATE_ZVAL`.
   - `Zend/zend_vm_def.h:9399-9430`: `ZEND_MAKE_REF` handler (`ZVAL_MAKE_REF_EX(op1, 2)` and `IS_INDIRECT` handling).
   - `Zend/zend_hash.c:2540-2745`: `zend_array_dup_value` (lines 2546–2560 conditional `IS_REFERENCE` unwrapping when `Z_REFCOUNT_P(data) == 1`), `zend_array_dup_ht_iterators`, `zend_array_dup_packed_elements`, `zend_array_dup`.
4. **`wch/r-source` (`94152790dbd49be40c28c1819f92370fb7581f0a`, R `4.7.0 Under development`)**:
   - `VERSION:1`: `4.7.0 Under development (unstable)`.
   - `src/include/Defn.h:184-243, 1415-1435`: `promsxp_struct`, `SEXPREC`, `VECTOR_SEXPREC`, `SWITCH_TO_REFCNT`/`REFCNTMAX`, `RCNTXT`.
   - `src/main/eval.c:954-1022`: `forcePromise` (`PRSEEN` 1/2 handling, `RPRSTACK`, `ENSURE_NAMEDMAX`, `SET_PRENV(e, R_NilValue)`) and `INCLNK_stack_commit`.
   - `src/main/coerce.c:2843-2938`: `substituteList`, `do_substitute` (including `R_GlobalEnv` suppression), `do_quote`.
   - `src/main/envir.c`: `do_parentframe`.
5. **`reactorlabs/rir` (`affbfc2feec0263ecb9c83b181d1b06388283340`)**:
   - `rir/src/runtime/Context.h:13-66`: `TypeAssumption` (`Arg0..5IsEager_`, `Arg0..5IsNonRefl_`, `Arg0..5IsNotObj_`, `Arg0..5IsSimpleInt_`, `Arg0..5IsSimpleReal_`) and `Assumption` enums.
   - `rir/src/compiler/opt/pass_scheduler.cpp:39-95`: `Initial` and `Speculation` optimization stages.
   - `rir/src/compiler/opt/force_dominance.cpp:18-65`: promise inlining preserving leaked `MkEnv` via synthesized `MkArg(exp, f')` + `StVar`, and `MissingArg` guard.
   - `rir/src/compiler/opt/elide_env.cpp:60-90` and `elide_env_spec.cpp:33-70`: `envNeeded` vs `envStubNeeded` and speculative environment elision for `SafeBuiltinsList::nonObject`.
6. **`Perl/perl5` (`40d4fc76b5f9cab20ca3914d2aa017863230719b`, Perl `5.45.5`)**:
   - `patchlevel.h:40-42`: `5.45.5`.
   - `sv.h:246-290, 418-534`: `struct sv`, `SvTYPE`, `SvUPGRADE`, `SVf_IOK`/`NOK`/`POK`/`ROK`, `SVs_GMG`/`SMG`/`RMG`/`VMG`, `SVf_PROTECT`/`READONLY`, `SVf_THINKFIRST`.
   - `op.h:82-185`: `OPf_WANT_VOID=1`, `OPf_WANT_SCALAR=2`, `OPf_WANT_LIST=3`, `GIMME_V`.
   - `pp_ctl.c:45-78`: `PP(pp_wantarray)` (`G_LIST` -> `&PL_sv_yes`, `G_SCALAR` -> `&PL_sv_no`, default -> `&PL_sv_undef`).
   - `mg.h:20-80` and `mg.c:616-769, 2968-3015`: `struct magic`, `MGVTBL`, `MGf_MGv2`, `MGf_GSKIP`, `Perl_mg_get`, `Perl_mg_set`, `Perl_magic_getpack`, `Perl_magic_setpack`.
   - `XSUB.h:158-175`: `dXSARGS` (`dSP; dAXMARK; dITEMS`).

### Peer-Reviewed Literature Verified

- Roberto Ierusalimschy, Luiz Henrique de Figueiredo, Waldemar Celes, *"The Implementation of Lua 5.0"*, J.UCS 11(7):1159–1176, 2005, DOI `10.3217/jucs-011-07-1159`.
- Andreas Gal et al., *"Trace-based Just-in-Time Type Specialization for Dynamic Languages"*, PLDI 2009, DOI `10.1145/1542476.1542528`.
- Floréal Morandat, Brandon Hill, Leo Osvald, Jan Vitek, *"Evaluating the Design of the R Language"*, ECOOP 2012, LNCS 7313:104–131, DOI `10.1007/978-3-642-31057-7_6`.
- Olivier Flückiger, Guido Chari, Jan Ječmen, Ming-Ho Yee, Jakob Hain, Jan Vitek, *"R Melts Brains: An IR for First-Class Environments and Lazy Effectful Arguments"*, DLS 2019, DOI `10.1145/3359619.3359744` (`arXiv:1907.05118`).
- Aviral Goel, Jan Vitek, *"On the Design, Implementation, and Use of Laziness in R"*, PACMPL 3 (OOPSLA), Article 153, 2019, DOI `10.1145/3360579` (`arXiv:1909.08958`).
- Olivier Flückiger et al., *"Contextual Dispatch for Function Specialization"*, PACMPL 4 (OOPSLA), Article 220, 2020, DOI `10.1145/3428288`.

### Reproducible Execution Micro-Probes (Observed 2026-11-19, Linux x86-64)

1. **Live Perl 5.40.1 probe (`perl v5.40.1 x86_64-linux-gnu-thread-multi`)**:
   - Minimal self-contained reproduction command:
     ```bash
     perl -MScalar::Util=dualvar -MDevel::Peek=Dump -e '
       use strict; use warnings;
       sub odd_list { return wantarray ? ("a", "role", "admin") : "safe"; }
       my %overwritten = (role => "guest", x => odd_list());
       print "overwritten: role=$overwritten{role}, x=$overwritten{x}\n";
       package CounterTie;
       sub TIESCALAR { my ($c,$v,$h)=@_; bless {val=>$v,fetches=>0,stores=>0,hook=>$h},$c }
       sub FETCH { my ($s)=@_; $s->{fetches}++; $s->{hook}->($s->{fetches}) if $s->{hook}; $s->{val} }
       sub STORE { my ($s,$v)=@_; $s->{stores}++; $s->{val}=$v }
       package main;
       my $y = 10;
       my $obj = tie my $x, "CounterTie", 5, sub { $y += 100 if $_[0] == 1 };
       my $sum1 = $x + $y; my $sum2 = $y + $x; $x = 7; my $d = defined($x);
       print "sum1=$sum1 sum2=$sum2 fetches=$obj->{fetches} stores=$obj->{stores} defined=$d\n";
       my $dv = dualvar(42, "forty-two"); Dump($dv); Dump($x);
     '
     ```
   - Observed output:
     - `Odd number of elements in hash assignment ...` followed by `overwritten: role=admin, x=a`.
     - `sum1=115 sum2=115 fetches=3 stores=1 defined=1`.
     - `Devel::Peek::Dump($dv)` -> `SV = PVNV`, `FLAGS = (IOK,POK,IsCOW,pIOK,pPOK)`, `IV = 42`, `PV = "forty-two"\0`.
     - `Devel::Peek::Dump($x)` -> `SV = PVMG`, `FLAGS = (GMG,SMG,RMG,IOK,pIOK)`, `MG_VIRTUAL = &PL_vtbl_packelem`, `MG_TYPE = PERL_MAGIC_tiedscalar(q)`.
2. **Executable LuaJIT 2.1 `LJ_GC64` NaN-boxing & PHP 8.x CoW/`IS_REFERENCE` Python 3.13.15 models**:
   - Minimal self-contained `LJ_GC64` bit-level check (`python3 -c '...'`):
     ```python
     import struct
     LJ_TISNUM = (~13) & 0xFFFFFFFF  # 0xfffffff2
     def itype_gc64(u64): return (struct.unpack("<q", struct.pack("<Q", u64))[0] >> 47) & 0xFFFFFFFF
     assert itype_gc64(0xfff8000000000000) == 0xfffffff0 < LJ_TISNUM  # canonical qNaN -> DOUBLE
     assert itype_gc64(0x0000000000000000) == 0x00000000 < LJ_TISNUM  # +0.0 -> DOUBLE
     assert itype_gc64(0x8000000000000000) == 0xffff0000 < LJ_TISNUM  # -0.0 -> DOUBLE
     assert itype_gc64(0xfffa0000deadbeef) == (~11 & 0xFFFFFFFF)      # unsanitized NaN -> LJ_TTAB!
     ```
   - Observed outputs across full test vectors: canonical qNaN `0xfff8000000000000` (`itype=0xfffffff0`), `+0.0` (`0x00000000`), `-0.0` (`0xffff0000`), `pi` (`0x00008012`), `+inf` (`0x0000ffe0`), `-inf` (`0xffffffe0`) all satisfy `itype < LJ_TISNUM`; encoded `LJ_TTAB(0x7f1234567890)` yields `0xfffa7f1234567890` (`itype=0xfffffff4`); unsanitized NaN `0xfffa0000deadbeef` decodes identically as `('LJ_TTAB', 'payload=0xdeadbeef', 'itype=0xfffffff4')`.
   - Verified `zend_array_dup_value` (`Zend/zend_hash.c:2546-2560`) executable Python state-machine model: active inner reference (`rc=2`) persists across `SEPARATE_ARRAY` (`a[0]=99, c[0]=99, r=99`, `a is not c`); after `unset($r)` (`rc=1`), `zend_array_dup_value` unwraps the reference (`a[0]=10, c[0]=99`, `c[0]` unboxed).

## Revalidation

To cheaply verify whether these findings still hold on newer upstream commits:

1. **Lua 5.5+ split-array & tagging**: Diff `lobject.h` (`struct TValue`, `struct Table`) and `ltable.h` (`getArrTag`, `getArrVal`, `lenhint`) against `lua/lua` `c42d820bc0c3bc4f2ad536e19d2f05405af10387`.
2. **LuaJIT NaN-boxing & FFI NaN canonicalization**: Check `src/lj_obj.h` (`LJ_TISNUM`, `itype`, `LJ_GCVMASK`) and `src/lj_cconv.c` (`lj_cconv_tv_ct` around `CTID_DOUBLE`) in `LuaJIT/LuaJIT` to see whether release-build NaN canonicalization has been added, and check `src/lj_snap.c` (`snap_unsink`) for `RID_SINK` changes.
3. **PHP CoW vs. `IS_REFERENCE` array duplication**: Inspect `Zend/zend_hash.c` (`zend_array_dup_value`) and `Zend/zend_types.h` (`_zval_struct`, `_zend_reference`, `SEPARATE_ARRAY`) in `php/php-src`; if a live `php` CLI binary is available, run `php -r '$a=[10,20]; $r=&$a[0]; $c=$a; $c[0]=99; echo "$a[0],$c[0]\n";'` (expect `99,99`) vs `php -r '$a=[10,20]; $r=&$a[0]; unset($r); $c=$a; $c[0]=99; echo "$a[0],$c[0]\n";'` (expect `10,99`).
4. **GNU R `PROMSXP` and RIR/PIR**: Diff `src/main/eval.c` (`forcePromise`) and `src/main/coerce.c` (`do_substitute`) in `wch/r-source`, and `rir/src/runtime/Context.h` + `rir/src/compiler/opt/force_dominance.cpp` in `reactorlabs/rir`.
5. **Perl 5 `wantarray`, `tie`, and `MGv2`**: Rerun the `wantarray` hash-injection and `CounterTie` + `Devel::Peek::Dump` probe under the target `perl` binary, and inspect `mg.h` / `mg.c` (`MGf_MGv2`, `Perl_mg_get`, `Perl_magic_getpack`) in `Perl/perl5` to track stabilization of v2 magic.
