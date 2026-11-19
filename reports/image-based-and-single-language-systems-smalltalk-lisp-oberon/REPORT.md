# Image-Based, Single-Language, and Content-Addressed Programming Systems: Smalltalk, Symbolics Genera, Mesa/Cedar, Project Oberon, and Unison

## Summary

Unix/C toolchains treat plain-text source files, file-shaped translation units, untyped string-matching linkers, `fork()`/`exec()` process isolation, and a sharp two-level store boundary between heaps and byte files as universal defaults. Four historical and modern lineages—**Smalltalk-80 / OpenSmalltalk Spur / Pharo**, **Symbolics 3600 / Genera**, **Xerox PARC Mesa/Cedar and ETH Project Oberon**, and **Unison**—prove none of those defaults is physically mandatory, while their failure modes and displacement postmortems isolate the irreducible constraints any successor must satisfy:

1. **Smalltalk-80 & Spur/Pharo VMs eliminate file/memory serialization at the cost of irreproducible image drift.** OpenSmalltalk's 64-bit Spur VM (`src/spur64.cog/cointerp.c`) snapshots live heaps—including `MethodContext` continuations and class/metaclass graphs—as raw relocatable segments (format `68021`/`68533`) and keeps direct-pointer `become:` fast via a partial read barrier (`isForwardedObjectClassIndexPun() == 8`). Pharo's `ShiftClassInstaller` migrates live instances atomically across layout edits, but imperative heap mutation plus `become:` produces reachable states unreachable from declarative source ("image drift"), and multi-developer workflows forced Pharo back onto Git-backed textual serialization (Monticello -> Iceberg/Tonel `.class.st`).
2. **Symbolics 3600/Genera lost to commodity silicon volume economics and tenant isolation, not semantic expressiveness.** The 3600 paired 36-bit tagged words (2-bit CDR code + 34-bit reference: 2-bit tag + 32-bit immediate, or 6-bit tag + 28-bit address; plus 7-bit physical ECC), 17-bit generic instructions with parallel tag/ALU checking, and page-table Ephemeral GC barriers with Genera's single-address-space OS (object-retaining Presentations and non-unwinding condition/restart negotiation). Even when the 3640 outperformed safety-disabled VAX/68020 Lisp runs by `1.75x–3.9x` at equal 200 ns cycles, larger commodity markets outpaced custom symbolic CPUs in cycle time and price/cycle (Moon 1987, p. 44), while portable C/Unix ("Worse is Better") and multi-tenant isolation demands dominated.
3. **Mesa/Cedar and Project Oberon refute the dichotomy between untyped linkers and mutable image drift.** Both are statically typed, source-rebuildable, single-language environments without offline untyped linkers or `fork()`/`exec()` per command. Mesa/Cedar verified 48-bit `(net, host, time)` `.bcd` interface stamps alongside `CHECKED`/`UNSAFE`/`TRUSTED` safety boundaries and `DF`/`BringOver` builds. Project Oberon (2013 RISC-5: **9,994 lines total** across OS, UI, compiler, graphics, net, and bootloader) uses `Oberon.Call` (`Module.Procedure`), cooperative zero-stack-scanning GC (`Kernel.Mark`), and `.smb` symbol files encoding hidden GC pointer offsets (`ORB.FindHiddenPointers`). Crucially, Project Oberon 2013 checks a **whole-module** 32-bit `.smb` checksum (`Modules.Load` `res = 3`), whereas Régis Crelier (1994, ETH Diss. 10650, OP2) refined this to **per-export** public/private (`PB`/`PV`) structural fingerprints—catching hidden size and hidden GC-pointer drift at constant struct size without invalidating non-consumers on additive exports.
4. **Unison's content-addressed AST store eliminates rename breakage and diamond symbol collisions while introducing graph-symmetry, hash-cascade, and FFI trade-offs.** Unison (`unisonweb/unison`) identifies definitions by version-tagged (`Tag 2`) SHA3-512 hashes of alpha-invariant de Bruijn ABTs + checked types (`#<base32hex>[.<pos>]`), decoupling names into SQLite namespace DAGs (`0` rebuilds on rename; simultaneous incompatible library versions). Source inspection exposes key boundaries: structurally symmetric mutually recursive cycles fail canonical ordering (`IncompleteElementOrderingError`), body edits cascade hashes (leading Unison to supersede long-lived `Patch` propagation with name-directed transitive re-typechecking in `Update2.hs`), and C FFI (`Unison.Runtime.Foreign.Dynamic`) reverts to nominal DLL paths, string symbols, and `libffi` `FFSpec` declarations.

## Applicability

This report synthesizes thirteen primary subjects (four pinned upstream Git repositories and nine primary publications) plus one runnable Python 3.10+ verification probe (`support/verify_image_and_hash_semantics.py`). Because each lineage evolved across major revisions, findings distinguish shared principles from version-specific mechanics:

- **Smalltalk-80 (1983) vs. OpenSmalltalk Spur64 & Pharo (2015–2026)**: Goldberg & Robson (1983, *Blue Book*) defines the 16-bit Object Table VM (32,768-object ceiling, reference counting + mark-sweep, O(1) OT `become:`). `OpenSmalltalk/opensmalltalk-vm` (`a0377cd04251fff81a613fe42e47cb2acda222f2`, `VMMaker.oscog-eem.3939`) and Miranda & Béra (ISMM '15) define the direct-pointer 64-bit Spur VM (formats `68021`/`68533`, forwarding pun `8`); note `opensmalltalk-vm` serves Squeak/Cuis and dropped Pharo/Newspeak VM builds in August 2025. Live class migration and FFI callouts are inspected in `pharo-project/pharo` (`c37e8dda7d7d76a5c92a7265ebbe77015193663e`).
- **Symbolics 3600 & Genera (1984–1987)**: Moon (1984, 1987) covers the 36-bit 3600 family; Walker, Moon, Weinreb & McMahon (1987) covers Genera; Gabriel (1989/1991) provides the contemporaneous portability analysis. Later 40-bit Ivory VLSI and DEC Alpha Open Genera are outside direct source scope.
- **Mesa/Cedar (1986) & Oberon (1989/1992/1994/2013)**: Swinehart et al. (1986) covers Cedar on Dorado/Dandelion workstations. Wirth & Gutknecht (1989, 1992) covers Ceres/NS32032 Project Oberon (~12,000 LOC); `Spirit-of-Oberon/ProjectOberon2013` (`72966ea608613dad76f5afdd57578c7e53741bd3`) provides exact Oberon-07 RISC-5 source (9,994 LOC, whole-module `.smb` checksums), contrasted with Crelier (1994, ETH Diss. 10650) per-export `PB`/`PV` fingerprints.
- **Unison (legacy `Patch` vs. 2026 `Update2`/`Upgrade`)**: `unisonweb/unison` (`b5c5188d99f31820d0cc012f194948d2876c14e7`) implements Hashing V2 (`Tag 2`, SHA3-512), SQLite schema v3, and `Update2.hs` (`useUpdateV2 = True`) superseding long-lived `Patch` workflows.

### Cross-References to Adjacent Corpus Packages

To avoid duplicating Rust-specific kernel, IDE, and build-graph analyses covered elsewhere in the corpus:
- Modern language-isolated OS kernels (SPIN, Singularity/Sing#, capability calculi, Rust OS isolation): see `metal-typechain-language-isolated-kernels-1995-2026`.
- Snapshot/view compiler-backed IDE architectures over plain-text files (RLS, `rust-analyzer`, `clangd`, Roslyn, `gopls`, Swift, TypeScript): see `language-server-snapshots-views-and-compiler-backed-ide-architectures`.
- Demand-driven incremental computation and build/query engines (Adapton, Self-Adjusting Computation, Salsa, `rustc` red-green queries, GHC recompilation, Buck2): see `incremental-computation-adapton-salsa-buck2-and-build-system-graphs`.

## Findings

### 1. Structural Taxonomy: Four Departures from the Unix/C Toolchain

Basis: normative + documentation + source + derived

| Dimension | Smalltalk-80 / Spur / Pharo | Symbolics 3600 / Genera | Xerox Mesa / Cedar | Project Oberon (1992/2013) + Crelier OP2 | Unison (`unisonweb/unison`) | Unix / C / ELF Baseline |
|---|---|---|---|---|---|---|
| **Source of Truth** | Live `.image` heap + `.changes` (Pharo round-trips to Git via Tonel `.class.st`) | Persistent virtual memory ("World Load") + SCT (`defsystem`) files | Versioned immutable files + `DF` manifests | `.Mod` source files + `.smb`/`.rsc` binaries | Content-addressed SQLite AST store; names as branch metadata | Plain-text files + line-diff VCS (Git) |
| **Compilation Unit** | Single `CompiledMethod` live in-image | Single function/form live from Zmacs | `DEFINITIONS` + `PROGRAM` modules | Single `.Mod` module compiled in-memory | Per-definition or mutually recursive SCC | File-shaped TU (`.c` + `#include`); batch |
| **Store Boundary** | Eliminated inside image (raw heap + `MethodContext` dump) | Eliminated inside World Load (demand-paged tagged VM) | Two-level store bridged by `DF` + Caching FS | Two-level store (files on disk, typed heap in RAM) | Immutable SQLite blobs (`object`, `causal`, `watch_result`) | Strict two-level store: byte files vs. volatile heap |
| **Link / Interface Identity** | Dynamic selector dispatch via Class Table; no offline linker | Dynamic symbol/function cells + Flavors; single address space | 48-bit `.bcd` `VersionStamp` `(net, host, time)` checked by `Binder` | 2013: whole-module 32-bit `.smb` key; OP2 (1994): per-export `PB`/`PV` FPs | SHA3-512 of canonical de Bruijn ABT + type (`#hash[.pos]`) | Untyped string matching (`ld`/`ld.so`); optional mangling |
| **Live Update / Migration** | `allInstances` + `become:` (Spur pun `8`); resumable `MethodContext` | Live redefinition; non-unwinding condition/restart protocol | Rebind `.bcd`; `Commander` calls | `Modules.Free` (`refcnt=0`) + reload; `Oberon.Call` (`M.P`) | Immutable; `Update2`/`Upgrade` re-typechecks dependents | Restart or `dlopen` (unsafe `dlclose`); frozen C ABI |
| **Protection Model** | Single VM address space; green processes | Single tagged address space; no kernel/user privilege wall | Single address space; `CHECKED` vs `UNSAFE`/`TRUSTED` | Single address space; cooperative loop; `SYSTEM` module | Managed runtime + algebraic abilities | Hardware MMU processes, rings, `fork()`/`exec()` |
| **FFI to C / OS** | High friction: pinning (`pinnedBitShift`), UnifiedFFI, single VM lock | Custom ISA lacked native C ABI | Self-contained Mesa/Cedar on Alto/Dorado | Self-contained RISC-5/Ceres; `SYSTEM.GET`/`PUT` | Reverts to nominal DLL path + string symbol + `libffi` | Native lingua franca (`psABI`, `libc`) |
| **Primary Failure / Limit** | Image drift, VCS friction pre-Tonel, stripping bloat, FFI | Commodity RISC/x86 silicon economics; no tenant isolation | Proprietary Xerox hardware; ecosystem scale | Single-user cooperative OS; `Modules.Free` heap-dangling hazard | Hash-cascade refactors, symmetric-cycle error, nominal FFI | Silent ABI/ODR bugs, `#include` reparsing, SemVer diamonds |

**Derived classification warrant**: Contrasting precedents (Cedar, Genera, Oberon, Smalltalk, Unison) prove textual `#include`, untyped linkers, batch-only compilation, `fork()`/`exec()` per command, and flat single-version symbol namespaces are **historically contingent** (derived from 1970s RAM and portability limits). Conversely, commodity semiconductor volume economics (Moon 1987, p. 44), hardware isolation against speculative side channels and untrusted native code (`metal-typechain-language-isolated-kernels-1995-2026`), declarative source reproducibility, and cyclic graph-automorphism limits (`ABT.hs:33–64`) represent **irreducible engineering constraints**.

---

### 2. Smalltalk-80 and Modern Spur/Pharo Virtual Machines

Basis: normative + documentation + source + execution

#### 2.1 Object Memory: Blue Book Object Table vs. OpenSmalltalk Spur64 Partial Read Barrier

In Goldberg & Robson (1983, Part Four), every Smalltalk-80 reference is a 16-bit Object Pointer (OOP): 1 tag bit distinguishes `SmallInteger` from a **15-bit Object Table (OT) index**, capping any image at $2^{15} = 32,768$ live heap objects. OT entries hold heap addresses, format flags, and reference counts (reclaiming acyclic garbage immediately, backed by mark-sweep for cycles). Indirection through the OT made `obj1 become: obj2` an $O(1)$ entry swap, at the price of double indirection on every slot access. Squeak V3 later removed the OT for direct pointers, making `become:` an $O(\text{heap size})$ full scan.

OpenSmalltalk's **Spur** memory manager (Miranda & Béra, ISMM '15, DOI `10.1145/2754169.2754186`), verified in `OpenSmalltalk/opensmalltalk-vm` (`a0377cd04251fff81a613fe42e47cb2acda222f2`, `src/spur64.cog/cointerp.c:2792–2856`), combines direct pointers with $O(1)$-per-object `become:` using a uniform 64-bit header and lazy forwarding guarded by a **partial read barrier**:

```text
Spur64 Immediate Pointer Tags (low 3 bits, tagMask=0x7, allocationUnit=8B):
  0=Heap oop | 1=SmallInteger (61-bit signed) | 2=Character | 4=SmallFloat (8-bit exp offset 896, 52-bit mantissa)

Spur64 Base Object Header (BaseHeaderSize=8 bytes, cointerp.c:2792-2856):
  [63..56] numSlots (8b; 255 => 8B overflow size word at obj-8) | [55] marked | [54] grey
  [53..32] identityHash (22b, mask 0x3FFFFF; doubles as Class Table index when object is a class)
  [31] unused | [30] pinned (prevents GC move for FFI) | [29] remembered (generational write barrier)
  [28..24] format (5b; 1=nonIndexablePtr, 2=Array, 3=indexablePtr, 4=Weak, 5=Ephemeron, 7=forwarded, 24+=CompiledMethod)
  [23] immutable | [22] extraAligned | [21..0] classIndex (22b into 2-level hiddenRootsObj Class Table, 1024 entries/page)
```

Reserved Class Table indices `0..31` encode VM puns: `0` (`isFreeObjectClassIndexPun`), `3` (`segmentBridgePun`), **`8` (`isForwardedObjectClassIndexPun`)**, and `16..31` (internal array/word/class puns).

In `SpurMemoryManager>>#become:with:twoWay:copyHash:` (`cointerp.c:47374–47445`), Spur dispatches to two paths:
1. **In-place swap (`inPlaceBecomeandcopyHashFlag`, `cointerp.c:52785–52848`)**: Used iff `numSlotsOf(obj1) == numSlotsOf(obj2)`, neither object is an active class in the Class Table (`o1ClassIndex + o2ClassIndex == 0`, since class forwarding triggers method-cache flushing), and neither is a `CompiledMethod` (which would break Cog JIT unmapping). Spur swaps headers—unswapping `rememberedBit` and conditionally unswapping `identityHash` per `copyHashFlag`—and swaps all payload slots with **0 forwarders**.
2. **Out-of-place cloning + lazy forwarding (`outOfPlaceBecomeandcopyHashFlag`, `cointerp.c:58121–58220`)**: For unequal sizes, classes, or methods, Spur clones `obj1 -> clone1` and `obj2 -> clone2`, overwrites `obj1`'s header with `classIndex = 8` and `format = 7`, clears `immutableBit`, stores `clone2` in slot 0 (updating the remembered set if old-to-young), and symmetrically forwards `obj2 -> clone1`.

Because `classIndex == 8` never hits in monomorphic/polymorphic inline caches, **fast-path message sends execute zero explicit read-barrier checks** (Miranda & Béra 2015). Inline-cache misses check `isOopForwarded` in one masked test (`!(oop & 0x7) && !(longAt(oop) & (0x3FFFFF - 8))`, `cointerp.c:47427–47429`) and follow slot 0 (`followForwarded:`); the next GC rewrites remaining pointers and reclaims forwarder stubs.

#### 2.2 Meta-Object Protocol, Live Image Snapshotting, and Pharo Schema Migration

Smalltalk-80 reifies classes, metaclasses, methods, and stack frames as ordinary heap objects (Goldberg & Robson 1983):
- **Parallel Metaclass Hierarchy**: Every class `C` is the sole instance of an anonymous metaclass `C class` mirroring `C`'s inheritance chain (`Behavior -> ClassDescription -> Class`), closing at `Metaclass class` being an instance of `Metaclass`. Methods compile incrementally into `CompiledMethod` objects installed live in `methodDict`.
- **Reified `MethodContext` Continuations & Image Snapshotting (`cointerp.c:78206–78260, 79931–80032`)**: Active stack frames materialize lazily as heap `MethodContext` objects, allowing an in-image debugger to inspect activations, recompile failing methods, and resume frames without `ptrace`/DWARF. To snapshot, `snapshot:` flushes native stack pages into heap contexts, empties `newSpace` (`assert(newSpaceIsEmpty())`, line 79972), **writes `trueObj` into `activeContext`'s return slot** (lines 78223–78234) so cold image resumption returns `true`, writes a 128-byte header (`BytesPerWord * 16`, format `68021` or `68533` for multi-bytecode sets per `src/ckformat.c:29–37, 306–318`) plus raw old-space segments (`writeImageSegmentsToFile`), then pops the live process stack and re-marries `activeContext` onto a fresh stack page (`marryContextInNewStackPageAndInitializeInterpreterRegisters`, line 78260).
- **Live Schema Migration (`pharo-project/pharo` `c37e8dda7d7d76a5c92a7265ebbe77015193663e`, `src/Shift-ClassBuilder/ShiftClassInstaller.class.st`)**:
  1. `migrateInstancesTo:` (lines 283–302) collects `self oldClass allInstances` (VM `allInstancesOf`, `cointerp.c:45758`), allocates instances of `newClass` copying matching hidden and visible slots by name (`copyObject:to:`, lines 85–114), and clears `isReadOnlyObject` on old instances so Spur permits forwarding (line 111).
  2. If the layout **shrank** (`ShInstanceShapeChanged.class.st:25–28`), `invalidateBlockClosuresWithReceivers:` (lines 173–185) scans all `FullBlockClosure` instances holding migrated receivers and replaces their `compiledBlock` with an error block, preventing out-of-bounds slot reads.
  3. Inside `valueUninterruptably` (lines 268–279), Pharo atomically executes `oldObjects elementsForwardIdentityTo: newObjects copyHash: true` (line 299) and forwards `{ oldClass. oldMetaclass }, oldClassVariables` to `{ newClass. newMetaclass }, newClassVariables` (lines 272–273), then restores read-only flags (line 301).

#### 2.3 Failure Postmortems

1. **Image Drift (Verified by Probe B)**: Because an image persists arbitrary imperative heap mutations alongside code, live singletons, closures, and class variables can diverge irreproducibly from current declarative class definitions. In Probe B (`support/verify_image_and_hash_semantics.py`), a `Counter` whose declarative source enforces `(count >= 0, origin == "source", acyclic)` undergoes a live `become:` swap to a self-referential instance `(-42, "workspace-hotfix-v0", cyclic=True)` and is snapshotted (`926` B). Cold reload preserves the drifted state intact, while exhaustive bounded replay from declarative source proves it is strictly unreachable—forcing production teams to treat images as disposable artifacts rebuilt from external source.
2. **Multi-Developer VCS Friction**: Sequential `.st` change sets (`fileOut`/`fileIn`) failed under concurrent edits, driving Smalltalk back to external source control: **Monticello** (`.mcz` package snapshots) and modern Pharo's **Iceberg + Tonel** (one `.class.st` text file per class in Git, as seen in `ShiftClassInstaller.class.st`) for standard three-way merges and pull-request review.
3. **Deployment Stripping Bloat**: Global dictionaries, symbols, and reflective metadata interlink IDE and application objects, making minimal headless deployment depend on kernel bootstrapping or fragile tree-shaking.
4. **C FFI & Threading Friction**: Moving GC requires object pinning (`pinnedBitShift = 30`) or external heap buffers; `UnifiedFFI` (`src/UnifiedFFI/FFICallout.class.st`) maintains a parallel C type-alias marshaller; and OpenSmalltalk executes Smalltalk single-threaded (its experimental multi-threaded build only hands off a global VM ownership lock across FFI calls, `README.md:77–95`).

---

### 3. Symbolics Lisp Machines: 3600 Tagged Hardware and the Genera Environment

Basis: normative + documentation + derived

#### 3.1 Symbolics 3600 Tagged Architecture and Hardware Ephemeral GC

David A. Moon (*Symbolics Architecture*, IEEE *Computer* 20(1):43–52, Jan. 1987, DOI `10.1109/MC.1987.1663443`) co-designed system, instruction, and processor architectures to deliver full runtime safety without software checking overhead:

- **36-Bit Tagged Words and 43-Bit Physical ECC Memory (Moon 1987, Fig. 1, pp. 46–47)**: Every memory word has a **2-bit CDR code** (`bits 35..34`, compressing linear lists by encoding `cdr-next`/`cdr-nil` inline to halve ordinary list storage) plus a **34-bit object reference** (`bits 33..0`):
  - *Immediate format*: 2-bit major tag (`bits 33..32`) + **32-bit immediate payload** (fixnum or single-float).
  - *Pointer format*: 6-bit tag (`bits 33..28`, 2-bit major + 4-bit minor) + **28-bit word address** (`bits 27..0`).
  - Physical DRAM adds **7 bits of ECC** (**43-bit** physical word); Moon calculates that 4 tag bits add 10% to RAM width and 11% to 256-word disk sectors (~128 B formatting overhead).
- **17-Bit Generic Instructions and Parallel Tag Datapath (Moon 1987, Fig. 9, pp. 47, 50–51)**: Fixed **17-bit** instructions (9-bit opcode + 8-bit argument) pack two per 36-bit word for code density and reduced paging. Generic `Add` executes in one cycle on the 3640 while simultaneously fetching operands from the hardware **stack buffer** and top-of-stack scratchpad, computing the 32-bit fixed-point sum + overflow check, starting the optional floating-point accelerator, and checking tags in the parallel **tag processor**. Non-fixnum types or overflow divert cleanly to microcode or Lisp trap handlers.
- **Three-Stack Calling Discipline (Moon 1987, p. 48)**: Each stack group has a **control stack** (top frames cached in a hardware stack buffer, 5 header words per frame plus caller/callee argument copies and locals), a **binding stack** (dynamic special variables), and a **data stack** (temporary stack allocations). Function entry vectors collaborate with microcoded `Call` for arity checks, optional defaults, `&rest`, and live debugging/redefinition metadata.
- **Hardware Page-Table Ephemeral GC (Moon 1984, LFP '84, DOI `10.1145/800055.802040`)**: Memory is partitioned into short-lived *ephemeral* spaces and older tenured spaces. Instead of software store barriers, VM page-table hardware records writes of ephemeral pointers into older pages, restricting minor-GC root scans to dirty old pages and maintaining interactive pause times.

#### 3.2 Genera: Single-Address-Space OS, Presentations, and Condition/Restart Protocol

Walker, Moon, Weinreb & McMahon (*The Symbolics Genera Programming Environment*, IEEE *Software* 4(6):36–45, Nov. 1987, DOI `10.1109/MS.1987.232087`) documents the Lisp OS atop the 3600:
- **Open Single-Address-Space Architecture**: OS kernel, networking, file system, Zmacs/ZWEI editor, compiler, and user programs share one GC-managed tagged virtual address space with no user/kernel privilege wall or byte-pipe serialization between tools.
- **Presentations (Typed Live UI Output)**: Dynamic Windows stores presentation types and live Lisp object pointers behind displayed output; invoking a typed command makes only type-compatible displayed objects mouse-selectable, replacing stringly-typed terminal pipelines.
- **World Loads & Incremental Compilation**: Persistent virtual-memory snapshots ("World Loads", including incremental layered worlds) coexist with file-based System Construction Tool (`defsystem`) builds and live per-function Zmacs patching.
- **Condition/Restart Protocol**: Decoupled (1) signaling a condition, (2) non-unwinding dynamic handler negotiation (`handler-bind`, inspecting or declining in the signaler's live frame context), and (3) named recovery continuations (`restart-case`), with `unwind-protect` guaranteeing cleanup only when an actual non-local unwind occurs.

#### 3.3 Displacement Postmortem: Commodity Silicon Economics and Tenant Isolation

1. **Commodity Silicon Volume Trap**: At equal 200 ns cycles (Moon 1987, p. 44), the 3640 beat a VAX 11/780 by `1.75x` (PSL) and `3.9x` (DEC CL) and a 10 MHz 68020 by `2.1x` (Lucid CL) on `Boyer` *with VAX/68020 safety checks disabled*, while the VAX beat the 3640 by `1.8x` (`2.1x` with FPA) on Whetstone Fortran. Yet Moon explicitly warned: *"Hardware technology of conventional machines will always be a couple of years ahead of symbolic hardware, in cycle time and price/cycle, because of the driving force of their larger market."* Moon's counterargument—that CPUs were `<25%` of system cost—failed as high-volume CMOS RISC and superscalar x86 CPUs outpaced custom Lisp processors in clock rate, IPC, and fab amortization, forcing Genera onto DEC Alpha software emulation (Open Genera).
2. **Portability ("Worse is Better")**: Gabriel (1989/1991, `dreamsongs.com/RiseOfWorseIsBetter.html`) showed how Unix/C's "New Jersey" strategy—prioritizing simple portable implementation over interface completeness (e.g., returning `EINTR` rather than ITS-style "PC loser-ing" syscall restart)—colonized commodity hardware and concentrated compiler-optimization talent on C/C++.
3. **No Multi-Tenant Hardware Isolation**: Built for a trusted single user (Moon 1987, p. 44), Genera's open single address space could not enforce hard isolation across untrusted tenants, native C code, or speculative side channels (`metal-typechain-language-isolated-kernels-1995-2026`).

---

### 4. Statically Typed Modular Single-Language Environments: Mesa/Cedar and Project Oberon

Basis: normative + documentation + source + execution

Mesa/Cedar and Project Oberon refute the assumption that rejecting Unix text headers, untyped linkers, and `fork()`/`exec()` requires sacrificing static typing or reproducible source compilation.

#### 4.1 Xerox PARC Mesa and Cedar

Swinehart, Zellweger, Beach & Hagmann (*A Structural View of the Cedar Programming Environment*, ACM TOPLAS 8(4):419–490, Oct. 1986, DOI `10.1145/6465.6466`) details Cedar's evolution from Mesa on Dorado/Dandelion workstations:
- **`.bcd` Modules and 48-Bit `VersionStamp`**: Separating `DEFINITIONS` interfaces from `PROGRAM` implementations, the compiler emitted Binary Configuration Descriptions (`.bcd`) tagged with globally unique **48-bit `VersionStamp`** triples `(net, host, time)` (`BcdDefs`). Client `.bcd` files recorded every imported interface's stamp; the C/Mesa **Binder** and dynamic loader rejected any stamp mismatch statically, preventing silent header/prototype drift.
- **`CHECKED` vs. `UNSAFE` / `TRUSTED` Safety**: Cedar layered traced garbage-collected references (`REF`, using deferred reference counting + backup trace-and-sweep with runtime types; Rovner, Xerox PARC CSL-84-7, 1985) alongside manual `POINTER`s. Normal code compiled `CHECKED`; low-level code explicitly opted into `UNSAFE` modules or audited `TRUSTED` blocks.
- **Reproducible Distributed Configuration (`DF` / `BringOver` / `SModel`)**: Description Files (`DF`) pinned immutable remote versions of every source `.mesa`, compiled `.bcd`, and nested `.df` file; `BringOver` populated local caches consistently and `SModel` published releases—preventing image drift inside a single-address-space environment (lightweight Mesa processes, Viewers, Tioga, `Commander`).

#### 4.2 Project Oberon (1992 / 2013): 9,994-Line Self-Hosting Stack

Wirth & Gutknecht (*The Oberon System*, SPE 19(9):857–893, 1989, DOI `10.1002/spe.4380190905`; *Project Oberon*, Addison-Wesley 1992, ~12,000 LOC on Ceres/NS32032; 2013 RISC-5 FPGA revision) distilled Cedar to extreme minimality. Direct measurement of `Spirit-of-Oberon/ProjectOberon2013` (`72966ea608613dad76f5afdd57578c7e53741bd3`, 27 core `.Mod` files) confirms **9,994 total lines**:
- **Inner core (1,353 lines)**: `Kernel.Mod` (271), `FileDir.Mod` (352), `Files.Mod` (505), `Modules.Mod` (225).
- **Outer core & UI (3,251 lines)**: `Input.Mod` (79), `Display.Mod` (190), `Viewers.Mod` (206), `Fonts.Mod` (115), `Texts.Mod` (532), `Oberon.Mod` (410), `MenuViewers.Mod` (208), `TextFrames.Mod` (861), `System.Mod` (418), `Edit.Mod` (232).
- **Self-hosting compiler + inspector (3,106 lines)**: `ORS.Mod` (312), `ORB.Mod` (433), `ORG.Mod` (1,120), `ORP.Mod` (990) = 2,855 compiler lines, plus `ORTool.Mod` (251).
- **Graphics, networking & boot (2,284 lines)**: `BootLoad.Mod` (201), `Graphics.Mod` (685), `GraphicFrames.Mod` (529), `Draw.Mod` (156), `SCC.Mod` (181), `Net.Mod` (375), `RS232.Mod` (69), `PCLink1.Mod` (88).

Four core mechanisms verified directly in `ORB.Mod`, `Modules.Mod`, `Oberon.Mod`, and `Kernel.Mod`:
1. **`.smb` Symbol Files with Hidden GC Pointer Offsets (`ORB.Mod:245–354`)**: `ORB.Export` serializes exported constants, variables, procedures, and structural types (record base, extension level `nofpar`, byte `size`, visible fields). For unexported record fields, `FindHiddenPointers` (`ORB.Mod:259–268, 285`) emits anonymous field entries recording exact byte offsets of every hidden pointer (recursing through nested private records/arrays) so client subclasses emit sound GC tables without seeing private source.
2. **Whole-Module `.smb` Key & Load-Time Fixups (`ORB.Mod:341–354`, `Modules.Mod:45–186`)**: `ORB.Export` pads `.smb` to 4 bytes and sums 32-bit words (`sum := sum + x`, lines 343–344). Body-only edits leave `sum = oldkey` (`0` client recompilations); interface changes abort with `"new symbol file inhibited"` (line 350) unless explicit `newSF` is set. `Modules.Load` checks `impmod.key = impkey` transitively (`Modules.Mod:73`), failing with `res = 3` and rolling back `refcnt` (lines 181–182) on mismatch, then patches `BL` branches (`fixorgP`), module-table offsets (`fixorgD`), and type descriptors (`fixorgT`) in RAM—no offline linker exists.
3. **Zero-`fork()` Command Activation (`Oberon.Mod:280–298`, `Modules.Mod:188–203`)**: Middle-clicking `M.P` in any text calls `Oberon.Call`, which dynamically loads `M` if absent (`Modules.Load`), resolves parameterless procedure `P` (`Modules.ThisCommand`), and calls `P` in the same address space with `Oberon.Par` pointing directly into the live `Texts.Text`.
4. **Cooperative Between-Command GC & Type Extension (`Oberon.Mod:172–186, 307–321, 360–391`, `Kernel.Mod:84–131`)**: `Oberon.Loop` runs `Oberon.GC` strictly **between commands when the stack is empty**, so `Kernel.Mark` traces only static `mod.ptr` roots via constant-space Deutsch-Schorr-Waite pointer reversal—**zero stack maps or safepoints**. UI dispatch uses checked record type extension (`CASE M OF InputMsg: ... | ControlMsg: ...`, `Oberon.Mod:174–185`), confining unsafety to `SYSTEM` (`ORB.Mod:420–432`).
- **Observed unloading hazard (`Modules.Mod:205–216`)**: `Modules.Free` unloads when `mod.refcnt = 0` without scanning heap instances or procedure variables for dangling type-descriptor/code references into the freed module.

#### 4.3 Whole-Module `.smb` Key vs. Crelier's Per-Export Fingerprints (1994)

Direct inspection of `ORB.Mod:343–353` clarifies a frequent historical conflation: Project Oberon 2013 hashes the **entire `.smb` file** into one module key, so adding an unrelated export invalidates all existing clients (`res = 3`). Régis Crelier (*Separate Compilation and Module Extension*, Diss. ETH Nr. 10650, 1994, OP2 compiler) refined this to **per-export** public (`PB`) and private/extension (`PV`) structural fingerprints. Probe C (`support/verify_image_and_hash_semantics.py`) compares all four regimes on two clients of `Display` (`ClientDrawOnly` importing `Draw` only vs. `ClientExtFrame` extending `Frame`):

| Evolution Scenario | `ClientDrawOnly` (Mesa / Oberon-2013 / Crelier / ELF) | `ClientExtFrame` (Mesa / Oberon-2013 / Crelier / ELF) | Consequence |
|---|---|---|---|
| **E1: Body-only edit** | `OK` / `OK` / `OK` / `OK` | `OK` / `OK` / `OK` / `OK` | Early cutoff under all four regimes. |
| **E2: Add unrelated export (`LogLevel`)** | `REJECT` / `REJECT` / **`OK`** / `OK` | `REJECT` / `REJECT` / **`OK`** / `OK` | Whole-module keys cascade rebuilds; Crelier allows zero-rebuild additive evolution. |
| **E3: Add private field (`Frame.size: 12->16`)** | `REJECT` / `REJECT` / **`OK`** / `OK` | `REJECT` / `REJECT` / **`REJECT`** / **`OK` (UNSAFE)** | Crelier rejects broken subclass layout while sparing `ClientDrawOnly`; ELF silently links corrupt code. |
| **E4: Swap private `INTEGER` -> `POINTER` (`size: 12->12`)** | `REJECT` / `REJECT` / **`OK`** / `OK` | `REJECT` / `REJECT` / **`REJECT`** / **`OK` (UNSAFE)** | Even at **identical byte size**, `FindHiddenPointers` changes Oberon-2013 key & Crelier `PV`, catching silent GC corruption. |
| **E5: Change `Draw` signature (`INTEGER->REAL`)** | `REJECT` / `REJECT` / **`REJECT`** / **`OK` (UNSAFE)** | `REJECT` / `REJECT` / **`REJECT`** / **`OK` (UNSAFE)** | All three typed regimes catch calling-convention drift deterministically. |

---

### 5. Content-Addressed Code Databases: Unison

Basis: source + execution + derived

#### 5.1 Hashing V2 and SQLite Codebase Architecture

Verified directly in `unisonweb/unison` at `b5c5188d99f31820d0cc012f194948d2876c14e7`:
- **SHA3-512 Versioned Token Stream (`Tokenizable.hs:37–38, 122–137`, `Hash.hs:69–72`)**: Every `accumulate` hashes `hashingVersion = Tag 2` followed by big-endian length-prefixed tokens via `SHA3_512` (64 bytes), formatted for display in lowercase unpadded Base32Hex.
- **Typed Term/Type Identity (`Reference.hs:78–176`, `Term.hs:99–160`)**: References are `ReferenceBuiltin Text` (`##Text.take`) or `ReferenceDerived (Id Hash Pos)` (`#<hash>` or `#<hash>.<pos>` for `Pos : Word64` in an SCC). `hashTermComponents` wraps terms in their checked type (`incorporateType`), domain-separates terms (`Tag 1`) from types (`Tag 0`), and makes `Pos == 0` references hash-transparent (`TermRef (ReferenceDerived h 0) -> h`, lines 142–147).
- **Alpha-Invariant ABT & SCC Canonicalization (`ABT.hs:74–217`)**: `hash'` uses de Bruijn indices (`[Either [v] v]`), erasing bound names and source spans. `hashComponents` topologically hashes SCCs; within a cycle, `doHashCycle` runs pass 1 with `permutationEnv = Left names : env` (collapsing intra-cycle references to index `0`), sorts members by resulting hash to fix a canonical order `permutedNames`, and runs pass 2 in `map Right permutedNames ++ env` to compute the SCC hash.
- **SQLite v3 Schema (`codebase2/codebase-sqlite/sql/create.sql:1–160`)**: Stores Base32Hex prefixes in `hash(id, base32 COLLATE NOCASE)`, version-indirected `hash_object`, immutable `object` blobs (`0 = Term Component`, `1 = Decl Component`, `2 = Namespace`, `3 = Patch`), Merkle-DAG `causal`/`causal_parent` namespace history, and hash-keyed `watch_result` caching pure test evaluations globally.

#### 5.2 Capabilities Verified by Execution (Probe A)

Executing Probe A (`support/verify_image_and_hash_semantics.py`) verifies:
- **Zero-Rebuild Renames**: `scale` (`#b3p2mt1bai`) and dependent `pipeline` (`#1nmuioaa89`) retain identical hashes (`rebuilds_on_rename = 0`) after alpha-renaming parameters, shifting source spans, and renaming top-level bindings in the namespace.
- **Diamond Dependency Coexistence**: Incompatible library versions `lib.math_v1.norm` (`#qtok71qbrt`, `x + 1`) and `lib.math_v2.norm` (`#t3amhe2mt5`, `x * 2`) execute together inside one program (`combined(5) == 16`) with zero symbol clash.
- **Asymmetric Mutual Recursion**: `is_even`/`is_odd` (distinguished by base cases `1` vs. `0`) hash deterministically into one SCC (`#2flp9ff79t` and `#2flp9ff79t.1`).

#### 5.3 Structural Trade-Offs Verified in Source

1. **Symmetric-Cycle Canonicalization Failure (`ABT.hs:33–64, 185–217`)**: Structurally isomorphic definitions inside an SCC produce identical pass-1 permutation hashes, triggering `IncompleteElementOrderingError` (issue `#2787`, workaround: insert a dummy distinguishing literal). Probe A reproduces this directly on symmetric `ping`/`pong` (`symmetric_cycle_detected: [['ping', 'pong']]`).
2. **Hash-Cascade Refactoring & Retreat from Long-Lived `Patch` Objects (`Update2.hs:85–360`, `Upgrade.hs:77–100`)**: Because dependents embed callee *body* hashes rather than stable module interface keys, leaf bug fixes alter hashes up the DAG. Modern Unison (`useUpdateV2 = True`) supersedes long-lived `Patch` objects with name-directed transitive-dependent re-typechecking (`getNamespaceDependentsOf`), spilling broken dependents to temporary `.u` scratch files on temporary `update-*` branches—reintroducing textual editing wherever breaking refactors require human judgment.
3. **Nominal C/OS FFI Boundary (`unison-runtime/src/Unison/Runtime/Foreign/Dynamic.hs:16–190`)**: `loadForeign` resolves external C code by nominal `DLL` path + string symbol (`getDLLPath dll ++ "$" ++ sym`) via `libffi` over flat C types (`I8..D64, Void, MBArr, Ptr, Fun`), manually rejecting unpromoted variadics (`BadVariadicArg`, lines 142–146) and `MBArr`/`Fun` returns (`BadResult`, lines 128–131). Cryptographic content identity stops at the OS ABI edge.
4. **Tooling & Review Isolation**: Replacing plain text with SQLite AST blobs forfeits standard text-tool interoperability (`git diff`, `grep`, PR review), requiring bespoke codebase managers (UCM, Unison Share) and illustrating why text-backed query compilers (`language-server-snapshots-views-and-compiler-backed-ide-architectures`, `incremental-computation-adapton-salsa-buck2-and-build-system-graphs`) keep content-addressed IR caches *derived* from text.

---

### 6. Historical Contingencies vs. Irreducible Constraints: Synthesis

Basis: derived

| Unix/C Assumption | Classification | Warrant (Precedent or Physical/Formal Law) | Takeaway for Modern & Verified Toolchains |
|---|---|---|---|
| **Textual `#include` interfaces** | **Contingent** | Disproved by Mesa `.bcd`, Oberon `.smb`, Crelier `PB`/`PV` FPs, and Unison typed AST refs. | Emit compiled, typed, hash-checked interface artifacts capturing layout and GC/ABI metadata. |
| **Untyped string-matching linkers** | **Contingent** | Disproved by Mesa `Binder`, Oberon `Modules.Load`, Crelier FPs; Probe C shows ELF silently accepts E3/E4/E5 corruption. | Enforce per-export structural/proof compatibility at link time so additive edits avoid rebuilds while ABI drift fails closed. |
| **Batch file-granular compilers** | **Contingent** | Disproved by Smalltalk/Genera live compilation, Oberon resident compiler, and modern query servers (`language-server-snapshots-views-and-compiler-backed-ide-architectures`). | Unify batch CI and interactive tooling over one immutable-snapshot query compiler (`incremental-computation-adapton-salsa-buck2-and-build-system-graphs`). |
| **`fork()`/`exec()` per command** | **Contingent** (single trust domain) | Disproved by `Oberon.Call`, Cedar `Commander`, Genera Presentations; **irreducible** across mutually untrusted tenants. | Decouple typed in-process modularity from hardware security domains. |
| **Flat single-version global symbols** | **Contingent** | Disproved by Unison hash-addressed diamond coexistence (Probe A). | Bind dependencies by cryptographic/interface identity while preserving interface boundaries for early cutoff. |
| **Mutable heap as sole source of truth** | **Fails Reproducibility** | Probe B image-drift witness + Smalltalk's migration to Monticello/Iceberg/Tonel Git files. | Treat live heaps and caches as derived/disposable projections of declarative source. |
| **Custom language-specific CPUs** | **Economically Constrained** | Moon (1987, p. 44) volume scaling + Gabriel (1989/1991) portability dynamics. | Target commodity ISAs with software/ISA-friendly tagging and barriers (e.g., Spur's partial read barrier). |
| **Multi-tenant & side-channel isolation** | **Irreducible** | Single-address-space language safety cannot contain untrusted C FFI or speculative leakage (`metal-typechain-language-isolated-kernels-1995-2026`). | Combine type/proof safety with hardware isolation across trust boundaries. |
| **C ABI & plain-text review ecosystem** | **Irreducible (Ecosystem)** | Evidenced by Pharo Tonel/UnifiedFFI and Unison `Update2.hs` scratch files / `Foreign.Dynamic`. | Provide lossless plain-text projection for review/archival and explicit typed adapter boundaries to C ABIs. |

## Boundaries

- **not examined**:
  - OpenSmalltalk Cogit JIT machine-code emission (`src/spur64.cog/cogit*.c`), Sista adaptive optimization, and Squeak/Pharo bytecode encoders beyond Spur headers, `become:`, and snapshotting.
  - Later Symbolics successors (40-bit Ivory VLSI, MacIvory, DEC Alpha Open Genera), MIT CADR microcode, and Interlisp-D.
  - Cedar's Tioga editor, Viewers window manager, Alpine transactional file server, and full Cedar release LOC counts.
  - Later Oberon descendants (ETH Oberon System 3 Gadgets, Active Oberon/A2, BlackBox, Franz–Kistler slim binaries), as well as Self, Factor, Forth, Erlang hot-loading, IBM System/38–IBM i single-level store, EROS, and Urbit.
  - Unison's ANF/JIT execution engine and Unison Share network sync protocol beyond Hashing V2, SQLite v3 schema, `Update2`/`Upgrade`, and `Foreign.Dynamic`.
- **unknown**:
  - Empirical incidence of `IncompleteElementOrderingError` across public Unison Share codebases (documented as an active issue in `ABT.hs:33–64`, unmeasured at corpus scale).
  - Full non-microbenchmark production overhead tables for Spur's partial read barrier beyond Miranda & Béra's ISMM '15 abstract/summary (paywalled full PDF tables not extracted).
  - Historical false-positive recompilation rates from Cedar's 48-bit timestamp `VersionStamp` on comment-only `DEFINITIONS` edits.
- **known not to apply**:
  - Single-address-space language isolation (Smalltalk, Genera, Cedar `CHECKED`, Oberon) is **known not to apply** as a confidentiality defense against speculative microarchitectural side channels or untrusted native C FFI extensions.
  - Oberon's zero-stack-scanning cooperative GC (`Oberon.GC` + `Kernel.Mark`) is **known not to apply** to preemptive multithreaded or multicore runtimes.
  - Probes A/B/C (`support/verify_image_and_hash_semantics.py`) are semantic models verifying exact algorithmic invariants, not wall-clock performance benchmarks of full VMs or type checkers.
- **unsupported**:
  - `OpenSmalltalk/opensmalltalk-vm` (`a0377cd04251fff81a613fe42e47cb2acda222f2`) dropped Pharo and Newspeak VM flavors in August 2025 (`README.md:72–75`), and its multi-threaded build does not support true parallel Smalltalk execution.
  - `Unison.Runtime.Foreign.Dynamic` (`b5c5188d99f31820d0cc012f194948d2876c14e7`, `Dynamic.hs:128–146`) rejects `MBArr`/`Fun` return types (`BadResult`) and unpromoted variadic scalar arguments (`BadVariadicArg`).
  - Project Oberon 2013 `Modules.Free` (`Modules.Mod:205–216`) does not track or invalidate live heap instances/procedure variables referencing unloaded modules, and `ORB.Mod` does not implement per-export fingerprints.

## Evidence

All observations were acquired and verified on `2026-11-19`.

### 1. Pinned Upstream Source Repositories

- **`OpenSmalltalk/opensmalltalk-vm`** (`a0377cd04251fff81a613fe42e47cb2acda222f2`, `VMMaker.oscog-eem.3939`):
  - `README.md:69–95`: Squeak/Cuis scope, Aug 2025 drop of Pharo/Newspeak, VMMaker simulation, single-VM-lock FFI threading.
  - `src/ckformat.c:25–37, 292–318`: Spur format codes (`6521`/`7033` 32-bit; `68021`/`68533` 64-bit).
  - `src/spur64.cog/cointerp.c`: header/tag macros (`L2792–2856`), `readImageFromFileHeapSizeStartingAt` (`L20517–20564`), `allInstancesOf` (`L45758–45833`), `become:with:twoWay:copyHash:` dispatch & `isOopForwarded` (`L47067–47445`), `inPlaceBecomeandcopyHashFlag` (`L52783–52848`), `outOfPlaceBecomeandcopyHashFlag` (`L58119–58220`), `snapshot:` & `writeImageFileIO` (`L78206–78260`, `L79931–80032`).
- **`pharo-project/pharo`** (`c37e8dda7d7d76a5c92a7265ebbe77015193663e`):
  - `src/Shift-ClassBuilder/ShiftClassInstaller.class.st`: `copyObject:to:` (`L85–114`), `invalidateBlockClosuresWithReceivers:` (`L173–185`), `migrateClassTo:` (`L241–280`), `migrateInstancesTo:` (`L283–302`).
  - `src/Shift-ClassBuilder/ShInstanceShapeChanged.class.st:15–33`; `src/UnifiedFFI/FFICallout.class.st:1–60`.
- **`Spirit-of-Oberon/ProjectOberon2013`** (`72966ea608613dad76f5afdd57578c7e53741bd3`):
  - `wc -l` across 27 core `.Mod` files = **9,994 lines** (Inner core 1,353: `Kernel` 271, `FileDir` 352, `Files` 505, `Modules` 225; Outer core/UI 3,251: `Input` 79, `Display` 190, `Viewers` 206, `Fonts` 115, `Texts` 532, `Oberon` 410, `MenuViewers` 208, `TextFrames` 861, `System` 418, `Edit` 232; Compiler 2,855 + `ORTool` 251: `ORS` 312, `ORB` 433, `ORG` 1,120, `ORP` 990; Graphics/Net/Boot 2,284: `BootLoad` 201, `Graphics` 685, `GraphicFrames` 529, `Draw` 156, `SCC` 181, `Net` 375, `RS232` 69, `PCLink1` 88).
  - `Sources/ORB.Mod` (`L245–354` `OutType`/`FindHiddenPointers`/`Export`, `L420–432` `SYSTEM`), `Sources/Modules.Mod` (`L45–216` `Load`/`ThisCommand`/`Free`), `Sources/Oberon.Mod` (`L172–186`, `L280–321`, `L360–391`), `Sources/Kernel.Mod` (`L84–131` `Mark`/`Scan`).
- **`unisonweb/unison`** (`b5c5188d99f31820d0cc012f194948d2876c14e7`):
  - `lib/unison-hash/src/Unison/Hash.hs:31–72`; `unison-core/src/Unison/Reference.hs:78–176`.
  - `unison-hashing-v2/src/Unison/Hashing/V2/{Tokenizable.hs:37–38,122–137; ABT.hs:33–217; Term.hs:99–160; Type.hs:47–62}`.
  - `codebase2/codebase-sqlite/sql/create.sql:1–160`; `unison-cli/src/Unison/Codebase/Editor/HandleInput/{Update2.hs:85–360, Upgrade.hs:77–100}`; `unison-runtime/src/Unison/Runtime/Foreign/Dynamic.hs:16–190`.

### 2. Verified Primary Publications

- Goldberg, A. & Robson, D. (1983). *Smalltalk-80: The Language and its Implementation*. Addison-Wesley, ISBN `978-0201113716`.
- Miranda, E. & Béra, C. (2015). "A Partial Read Barrier for Efficient Support of Live Object-Oriented Programming." *ISMM '15*, DOI `10.1145/2754169.2754186`.
- Moon, D. A. (1984). "Garbage Collection in a Large Lisp System." *ACM LFP '84*, pp. 235–246, DOI `10.1145/800055.802040`.
- Moon, D. A. (1987). "Symbolics Architecture." *IEEE Computer* 20(1):43–52, DOI `10.1109/MC.1987.1663443` (verbatim PDF inspected).
- Walker, J. H., Moon, D. A., Weinreb, D. L., & McMahon, M. (1987). "The Symbolics Genera Programming Environment." *IEEE Software* 4(6):36–45, DOI `10.1109/MS.1987.232087`.
- Swinehart, D. C., Zellweger, P. T., Beach, R. J., & Hagmann, R. B. (1986). "A Structural View of the Cedar Programming Environment." *ACM TOPLAS* 8(4):419–490, DOI `10.1145/6465.6466` (with Rovner, P. M., 1985, Xerox PARC CSL-84-7).
- Wirth, N. & Gutknecht, J. (1989). "The Oberon System." *SPE* 19(9):857–893, DOI `10.1002/spe.4380190905`; *Project Oberon* (Addison-Wesley, 1992, ISBN `978-0201544282`; ETH Zurich, 2013).
- Crelier, R. B. J. (1994). *Separate Compilation and Module Extension*. Diss. ETH Nr. 10650, ETH Zurich.
- Gabriel, R. P. (1989/1991). "Lisp: Good News, Bad News, How to Win Big" ("The Rise of Worse is Better"), *AI Expert* 6(6):30–35 (`https://www.dreamsongs.com/RiseOfWorseIsBetter.html`).

### 3. Executable Probe (`support/verify_image_and_hash_semantics.py`)

Executed with Python 3 stdlib only (`exit 0`, `2026-11-19`):

```console
python3 -B reports/image-based-and-single-language-systems-smalltalk-lisp-oberon/support/verify_image_and_hash_semantics.py
```

```text
[PASS] Probe A (Unison SHA3-512 ABT hashing & diamond coexistence):
       scale=#b3p2mt1bai pipeline=#1nmuioaa89 (0 rebuilds on alpha/namespace rename)
       diamond norm v1=#qtok71qbrt vs v2=#t3amhe2mt5 -> combined(5)=16
       symmetric cycle ambiguity detected: [['ping', 'pong']]; asymmetric even/odd: {'is_even': '#2flp9ff79t', 'is_odd': '#2flp9ff79t.1'}
[PASS] Probe B (Smalltalk/Spur become: forwarding & image-drift witness):
       migrated Point slots=[3, 4, 99] identity_hash_preserved=True misses_before_gc=8 reclaimed=5
       image-drift witness state=[-42, 'workspace-hotfix-v0', True] unreachable_from_source=True (snapshot=926B)
[PASS] Probe C (Mesa .bcd / Oberon-2013 .smb / Crelier PB+PV / Untyped ELF):
       Display v0 Oberon-2013 key=0x41eb47cc Crelier FPs={'Frame': {'pb': '0xb74cf0c4', 'pv': '0xe2db1873'}, 'Draw': {'pb': '0x453625ae', 'pv': '0x453625ae'}}
       E1_body_only_edit                      | DrawOnly[M=OK, O=OK, C=OK, ELF=OK] | ExtFrame[M=OK, O=OK, C=OK, ELF=OK]
       E2_add_unrelated_export                | DrawOnly[M=REJECT, O=REJECT, C=OK, ELF=OK] | ExtFrame[M=REJECT, O=REJECT, C=OK, ELF=OK]
       E3_hidden_field_size_drift             | DrawOnly[M=REJECT, O=REJECT, C=OK, ELF=OK] | ExtFrame[M=REJECT, O=REJECT, C=REJECT, ELF=OK]
       E4_hidden_gc_pointer_drift_same_size   | DrawOnly[M=REJECT, O=REJECT, C=OK, ELF=OK] | ExtFrame[M=REJECT, O=REJECT, C=REJECT, ELF=OK]
       E5_draw_signature_abi_change           | DrawOnly[M=REJECT, O=REJECT, C=REJECT, ELF=OK] | ExtFrame[M=REJECT, O=REJECT, C=REJECT, ELF=OK]
```

## Revalidation

1. **Re-run the preserved semantic probe** (`<1s`, verifies Probes A, B, and C):
   ```console
   python3 -B reports/image-based-and-single-language-systems-smalltalk-lisp-oberon/support/verify_image_and_hash_semantics.py --json
   ```
2. **Diff OpenSmalltalk Spur invariants** against `a0377cd04251fff81a613fe42e47cb2acda222f2`: inspect `src/ckformat.c` (format codes `68021`/`68533`) and `src/spur64.cog/cointerp.c` (`isForwardedObjectClassIndexPun`, `inPlaceBecomeandcopyHashFlag`, `outOfPlaceBecomeandcopyHashFlag`, `writeImageFileIO`).
3. **Diff Pharo live schema migration** against `c37e8dda7d7d76a5c92a7265ebbe77015193663e`: inspect `src/Shift-ClassBuilder/ShiftClassInstaller.class.st` and `src/UnifiedFFI/FFICallout.class.st`.
4. **Diff Unison hashing, refactoring, and FFI** against `b5c5188d99f31820d0cc012f194948d2876c14e7`: inspect `Tokenizable.hs` (`hashingVersion`), `ABT.hs` (`IncompleteElementOrderingError`), `Update2.hs` (`useUpdateV2`), and `Unison/Runtime/Foreign/Dynamic.hs` (`FFType`, `prepareSpec`).
