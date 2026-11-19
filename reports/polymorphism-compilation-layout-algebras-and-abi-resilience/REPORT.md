# Polymorphism Compilation, Layout Algebras, and ABI Resilience

## Summary

Compiling parametric and ad-hoc polymorphism navigates a three-way trade-off among **(1) unboxed inline representation and direct dispatch**, **(2) separate compilation, polymorphic recursion, and binary-stable ABI evolution across dynamic-library boundaries**, and **(3) bounded code size, local rebuilds, and modular pre-monomorphization error checking**. Production compilers occupy six distinct points in this space: whole-type monomorphization (Rust, C++, MLton, Zig), uniform pointer boxing (OCaml, erased JVM, lifted GHC), intensional type analysis ($\lambda_i^{\mathrm{ML}}$, TIL), hybrid canonical reference-type sharing with JIT value-type specialization (.NET CoreCLR), GCShape stenciling with compile-time static dictionaries (Go 1.18+), and unboxed witness passing via Type Metadata and Value Witness Tables (Swift ABI resilience, with opt-in `@inlinable`/`@frozen` specialization inside resilience domains).

In systems languages lacking a compile-time polymorphic layout algebra, hiding layout, padding, alignment, and pointer metadata behind monomorphic compiler internals produces recurring soundness and modularity failures:

1. **Affine-Ceiling Slice-DST Closure and Injectivity**: Any nested combination of `#[repr(C)]`, `#[repr(packed(p))]`, and `#[repr(align(m))]` structs ending in `[T]` has exact size $S(n) = C + \mathrm{round\_up}(r + nE, A)$ in a four-word normal form (`offset`, `elem_size`, `size_base`, and `RoundingAlignAndPhase` packing $A \mid r$ in one `NonZeroUsize`, where $A \ge \mathrm{align}(\text{struct})$ and $0 \le r < A$). This form is **strictly closed** under arbitrary field extension and outer rounding (`38,060` configurations verified). Moreover, $n \mapsto S(n)$ is injective on $\mathbb{N}$ **if and only if** $E \ge A$ (`713` `(A, r, E)` triples verified). When $0 < E < A$, the Pigeonhole Principle forces at least $A - E \ge 1$ adjacent plateau pairs $S(n) = S(n+1)$ per period of $A$ elements. Reconstructing metadata from byte length across plateaus fabricated out-of-bounds slices in `google/zerocopy` (fixed in commit `12f746d2307c30455db1875b9b80e45ada5b8675`), and flattening nested rounding to outer alignment understated sizes (fixed in commit `242ff08b5cf0d7723c0bc29ccfac0628b967d794`).
2. **Decidable Polymorphic Padding Algebras**: Without stabilized `generic_const_exprs` or `size_of_val_raw`, Rust derive macros fall back to hygiene oracles (`Identity<Type = T>`), homogeneous-field proofs, over-strong `Unaligned` bounds, or Post-Monomorphization Error (PME) `const` assertions. Universal interior- and trailing-padding freedom over `repr(C)`/`packed(k)`/`align(m)` generics is decidable via a finite power-of-two small-model solver—which surfaces aligned ZST counterexamples (`[u16; 0]`) and proves that $\mathrm{Align}(T) \ge \mathrm{Align}(U)$ eliminates *interior* padding in `(T, U)` while leaving *trailing* padding unless $\mathrm{Align}(T) \mid \mathrm{Size}(U)$.
3. **Static Representation Discipline vs. Dynamic Value Witnesses**: GHC's `TYPE (r :: RuntimeRep)` and `BoxedRep Levity` statically require concrete register/stack representations at every term binder and argument (`hasFixedRuntimeRep` via `ConcreteTv`), permitting representation-polymorphic *results* while rejecting opaque binders. Swift makes the dual choice: opaque types pass indirectly by address alongside 15-entry Value Witness Tables separating unpadded `size` from padded `stride` (enabling cross-struct tail-padding reuse and cascading single-payload enum extra inhabitants).
4. **Reference-Admissible Nondeterministic Layout Refinement**: Unspecified default layouts (`repr(Rust)`) are faithfully modeled as bounded demonic nondeterminism over all reference-admissible layouts, refined downward by concrete compiler versions, separating portable proofs from compiler-version coincidences.

---

## Applicability

This report synthesizes 14 primary subjects pinned in `REPORT.json`:

- **Swift ABI resilience**: `swiftlang/swift@3be0cf4b450b5366cff4b1a7e5bf7e5b4633224f` (ABI headers, runtime C++, and ABI/evolution docs). `ValueBuffer` sizes (`24`B, align `8`) reflect 64-bit targets (`NumWords_ValueBuffer = 3`); enum byte examples assume little-endian (`EnumImpl.h` branches on `__BIG_ENDIAN__`).
- **GHC representation/levity polymorphism**: Eisenberg & Peyton Jones (PLDI '17) compared with `ghc/ghc@83038fbee5efea8e3ebd5090b2ff5537462e169d` (`BoxedRep Levity` split and `ConcreteTv` constraints).
- **Intensional analysis & hybrid sharing**: Harper & Morrisett (POPL '95), Tarditi et al. (PLDI '96), Kennedy & Syme (PLDI '01) paired with `dotnet/runtime@db341b0b461356d954079d27e86cb47c929e7e8a`, and `golang/proposal@83ee2aaf9fdcc1a1cf4bb4d20216fc979635cf04`.
- **Rust layout, pointer metadata, monomorphization, and `zerocopy` slice-DST algebra**: `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` (RFC 2580), `rust-lang/rust@b0b600668bb9b4a897e2299b0a44289d42276545`, and `google/zerocopy` (`main@ec133ce4d7993775413d852f91c9e3eb2a2a0897`, plus fix commits `12f746d2307c30455db1875b9b80e45ada5b8675` and `242ff08b5cf0d7723c0bc29ccfac0628b967d794`).
- **Executable verification**: `support/verify_layout_algebra_and_witnesses.py` (Python 3.10+, stdlib only) checks every VWT invariant, affine-ceiling closure/injectivity claim, `zerocopy` counterexample, padding decision, and `repr(Rust)` nondeterminism check.

**Adjacent corpus packages (cross-referenced, not duplicated)**:
- `rustc-layout-computation-target-datalayouts-and-parametricity` (`rustc_abi` / `rustc_ty_utils` layout tables and target datalayouts),
- `rustc-monomorphization-vtables-statics-symbols-and-cgu-partitioning` (`rustc` monomorphization collector, vtables, statics, CGU partitioning),
- `anneal-forward-compatible-mir-semantics-and-reference-admissible-refinement` (mechanized forward-compatible MIR refinement lattice).

---

## Findings

### 1. The Polymorphism Compilation Triangle and Six Concrete Compilation Strategies

Basis: normative + documentation + source + derived

Lowering a polymorphic definition $f : \forall \alpha.\; \tau(\alpha)$ to machine code requires resolving **(i) representation** (size, alignment, register class, GC/pointer map, copy/move/drop rules), **(ii) dispatch** (trait/protocol methods and primitive operators), and **(iii) frame/container allocation** (static offsets vs. dynamic stack/heap buffers). These choices form an irreducible trade-off triangle:

- **Vertex A (Unboxed Inline Performance)**: Values of $\alpha$ live unboxed in registers, stack frames, and contiguous arrays with direct, inlinable dispatch.
- **Vertex B (Separate Compilation and ABI Resilience)**: Generic code compiles once into a `.so`/`.dylib` without downstream type arguments, supporting polymorphic recursion and layout evolution across dynamic-library boundaries.
- **Vertex C (Bounded Code Size and Modular Checking)**: Binary size scales as $O(|\text{fns}|)$ instead of $O(|\text{types}| \times |\text{fns}|)$, rebuilds stay local, and layout/semantic errors reject at the generic definition rather than as Post-Monomorphization Errors (PMEs).

| Strategy | Systems | Generic `T` Representation | Sharing Equivalence Class | Poly. Recursion | Cross-DSO Unspecialized ABI | PME Surface | Primary Runtime / Compile Cost |
| --- | --- | --- | --- | --- | --- | --- | --- |
| **Monomorphization** | Rust, C++, MLton, Zig | Unboxed, inline, target-optimal | Exact concrete type tuple | Rejected | No (body/IR exported) | High (`const` / template traps) | $O(\lvert\text{types}\rvert \times \lvert\text{fns}\rvert)$ codegen, ICache bloat, non-local rebuilds |
| **Uniform boxing** | OCaml, erased Java, lifted GHC | Uniform 1-word GC/tagged ptr | All boxed/erased types | Supported | Yes (fixed pointer ABI) | None | Heap allocation, pointer chasing, boxed numeric arrays |
| **Intensional type analysis** | $\lambda_i^{\mathrm{ML}}$, TIL | Unboxed via runtime `typecase` | Single body + optional spec. | Supported | Possible with fixed type ABI | None | Runtime type-term construction/branching unless specialized |
| **Canonical sharing + JIT spec.** | .NET CoreCLR (C#, F#) | Shared 1-word ref; specialized structs | Canonical ref (`__Canon`) vs. exact struct | Supported (lazy JIT) | Yes (CIL + runtime JIT) | None for layout | JIT time, dict lookup on ref generics, fragile GC stackwalk |
| **GCShape stenciling + static dicts** | Go 1.18+ | Unboxed inline per GCShape | Underlying type or pointer shape | Rejected (static RO dicts) | No (body + proto-dict exported) | Low | Indirect `itab`/dict calls inhibit inlining & escape analysis |
| **Value Witness Tables + resilience** | Swift | Unboxed in memory; indirect by address | Single body + `@inlinable` spec. | Supported (lazy metadata) | Yes (stable ABI + evolution) | None at ABI | Indirect address-only ABI, VWT calls, reabstraction thunks |

#### 1.1 Whole-Type Monomorphization, PMEs, and Removal of `-Zpolymorphize`

Basis: source + documentation + derived

Whole-type monomorphization (`rustc`, C++ templates) clones and specializes each generic body per reachable concrete type tuple, yielding optimal register allocation and direct dispatch at three structural costs:

1. **No polymorphic binary boundary**: Generic functions cannot cross a dynamic-library boundary without shipping IR/headers or erasing types behind a trait object (`&dyn Trait`).
2. **Post-Monomorphization Errors (PMEs)**: Checking preconditions via `const { assert!(...) }` or layout queries inside generic bodies lets libraries type-check cleanly while failing inside downstream instantiations (e.g., ZST slice elements). `#[track_caller]` does not localize PMEs, and formal verifiers gated on monomorphization admission must prove CTFE non-stuckness to prevent vacuous soundness.
3. **Removal of `-Zpolymorphize`**: In `rust-lang/rust@b0b600668bb9b4a897e2299b0a44289d42276545` (`compiler/rustc_monomorphize/src/lib.rs:15-21`), `rustc_monomorphize` contains only `collector`, `diagnostics`, `graph_checks`, `mono_checks`, `offload`, `partitioning`, and `util`. The experimental `-Zpolymorphize` pass was deleted (`rust-lang/compiler-team` MCP #810; `rust-lang/rust` issue #124962) because partial post-hoc polymorphism conflicted with post-monomorphization MIR optimizations and crate monomorphization invariants (see `rustc-monomorphization-vtables-statics-symbols-and-cgu-partitioning`).

#### 1.2 Uniform Pointer Boxing

Basis: documentation + derived

OCaml, type-erased JVM generics, and lifted Haskell values erase type parameters by giving every polymorphic value a uniform pointer-sized representation. Separate compilation, compact code, and polymorphic recursion come for free, at the cost of heap indirection, extra GC traffic, and loss of dense unboxed generic value arrays.

#### 1.3 Intensional Type Analysis ($\lambda_i^{\mathrm{ML}}$ and TIL)

Basis: normative + documentation + derived

Harper & Morrisett (POPL '95, pp. 130–141, DOI `10.1145/199448.199475`) introduced $\lambda_i^{\mathrm{ML}}$, passing runtime type terms explicitly into polymorphic functions with two typed primitives: **`typecase`** (term-level dynamic dispatch on type structure that refines each branch's static type) and **`Typerec`** (constructor-level primitive recursion computing specialized representation types). Tarditi et al. (PLDI '96, *TIL*, pp. 181–192, DOI `10.1145/235805.235830`) deployed intensional type analysis in ML for unboxed arrays, flattened arguments, and mostly tag-free GC under separate compilation. Crucially, unlike Swift's behavioral Value Witness Tables, structural `typecase` inspects a *closed* universe of type constructors and breaks abstraction if a library evolves a public struct's hidden fields across binary releases.

#### 1.4 .NET CoreCLR Canonical Sharing and Value-Type JIT Specialization

Basis: documentation + source

Kennedy & Syme (PLDI '01, pp. 1–12, DOI `10.1145/378795.378797`) and modern CoreCLR (`dotnet/runtime@db341b0b461356d954079d27e86cb47c929e7e8a`) combine exact runtime types (`TypeHandle`/`MethodTable` preserved for casts, reflection, and GC) with representation-partitioned JIT code generation:

- **Canonical reference sharing vs. struct specialization**: Reference types share identical pointer layout and GC semantics, so CoreCLR compiles one shared native body across all reference instantiations (`Hashtable<string, int>` and `Hashtable<object, int>` share one layout/code body, while `Hashtable<int, string>` and `Hashtable<int, object>` share another; `src/coreclr/vm/genericdict.h:38-44`). Value types (structs/primitives) trigger per-type JIT specialization for inline unboxed storage.
- **Runtime dictionaries**: Shared code receives a `Dictionary` handle (`genericdict.h:18-64`) caching lazily populated slots (`TypeHandleSlot`, `MethodDescSlot`, `MethodEntrySlot`, `ConstrainedMethodEntrySlot`, `DispatchStubAddrSlot`, `FieldDescSlot`, `DeclaringTypeHandleSlot`), with `DictionaryLayout` stored on shared `EEClass` or `InstantiatedMethodDesc`.
- **GC stackwalker coupling**: Avoiding duplicate native code that differs only in GC maps requires CoreCLR's stackwalker to walk method signatures while threads are suspended—without allocating or taking locks—to compute valuetype stack sizes and GC roots (`docs/design/coreclr/botr/type-system.md:164-195`), an explicitly documented fragile runtime invariant.

#### 1.5 Go GCShape Stenciling and Compile-Time Static Dictionaries

Basis: documentation + source

Go 1.18+ (`golang/proposal@83ee2aaf9fdcc1a1cf4bb4d20216fc979635cf04`, `design/generics-implementation-gcshape.md`, `design/generics-implementation-dictionaries-go1.18.md`) implements an AOT hybrid:

- **Fine-grained GCShapes**: Two concrete types share a *shape instantiation* iff they have the same underlying type (avoiding dictionary callbacks for arithmetic/shift operators and keeping interfaces disjoint from non-interfaces) or are both pointers (mapped to `go.shape.*uint8_<param_idx>`, indexed by parameter position to preserve substitutability; `dictionaries-go1.18.md:16-35`).
- **Static RO-data dictionaries**: Every generic call passes a hidden `.dict` pointer as its first argument (`line 76`) pointing to a linker-deduplicated RO-data struct (`main..dict.Map[int,bool]`) holding: (1) concrete `*runtime._type` args, (2) derived `*runtime._type`s (`*T`, `[]T`, `map[K]V`), (3) sub-dictionaries for nested generic calls/closures, and (4) `itab` pointers for `OCONVIFACE`, interface-bound method calls, type assertions, and type switches (`lines 38-54`).
- **AOT limits**: Because dictionary layouts depend on inspecting the generic *body*, callers need exported generic bodies/proto-dictionaries—precluding cross-DSO and assembly generic instantiations (`gcshape.md:37`, `dictionaries-go1.18.md:118`). Static dictionary allocation also rejects non-monomorphisable polymorphic recursion (`dictionaries-go1.18.md:62-64`), register calling conventions can split within one GCShape (`struct { x, y int }` vs. `[2]int`, `gcshape.md:239`), and indirect `itab` dispatch blocks inlining and weakens escape analysis (`gcshape.md:235`).

---

### 2. Swift ABI Resilience: Unboxed Generics via Value Witness Tables and Resilience Domains

Basis: normative + documentation + source + execution

Swift (`swiftlang/swift@3be0cf4b450b5366cff4b1a7e5bf7e5b4633224f`) compiles unspecialized generic code and resilient library types *without* uniform heap boxing, while allowing full monomorphic specialization inside version-locked resilience domains or on `@inlinable`/`@frozen` opt-ins.

#### 2.1 Type Metadata Header and Value Witness Table ABI

Basis: source + normative

Every concrete type has a canonical `TargetMetadata` pointer (`include/swift/ABI/Metadata.h:265-286`) storing `Kind`/class-ISA at offset `0`. At negative offset `-1` word (`FullMetadata<T> : T::HeaderType, T`, `Metadata.h:160-214`), `TargetTypeMetadataHeaderBase` holds `ValueWitnesses`, pointing to `TargetValueWitnessTable<Runtime>` (`include/swift/ABI/ValueWitnessTable.h:132-239`), shareable across types with identical layout/value semantics (`ABIStabilityManifesto.md:253`). Its 15 slots (`include/swift/ABI/ValueWitness.def:97-294`, with slots 12–14 present iff `HasEnumWitnesses` is set) are:

| Slot | Kind | Witness (`ValueWitness.def`) | ABI Signature / Type | Role |
| --- | --- | --- | --- | --- |
| 0 | Fn | `initializeBufferWithCopyOfBuffer` | `T* (*)(B*, B*, M*)` | Copy-init fixed `ValueBuffer` (inline or side-allocated) |
| 1 | Fn | `destroy` | `void (*)(T*, M*)` | Destroy live inline object; storage becomes uninitialized |
| 2 | Fn | `initializeWithCopy` | `T* (*)(T*, T*, M*)` | Copy-init uninitialized `dst` from valid `src` |
| 3 | Fn | `assignWithCopy` | `T* (*)(T*, T*, M*)` | Copy-assign valid `src` onto valid `dst` |
| 4 | Fn | `initializeWithTake` | `T* (*)(T*, T*, M*)` | Destructive move to uninitialized `dst`; `src` invalidated |
| 5 | Fn | `assignWithTake` | `T* (*)(T*, T*, M*)` | Destructive move onto valid `dst`; old `dst` destroyed |
| 6 | Fn | `getEnumTagSinglePayload` | `unsigned (*)(const T*, unsigned, M*)` | Decode single-payload enum tag (`0` = payload) |
| 7 | Fn | `storeEnumTagSinglePayload` | `void (*)(T*, unsigned, unsigned, M*)` | Encode single-payload enum tag (XI or extra tag bytes) |
| 8 | Data | `size` | `StoredSize` (`size_t`) | Byte size **without** trailing alignment padding |
| 9 | Data | `stride` | `StoredSize` (`size_t`) | Array spacing: `max(1, round_up(size, align))` |
| 10 | Data | `flags` | `TargetValueWitnessFlags` (`uint32_t`) | Alignment mask + POD/inline/takable/copyable/enum flags |
| 11 | Data | `extraInhabitantCount` | `uint32_t` (max `0x7FFFFFFF`) | Invalid bit patterns usable by enclosing enums |
| 12 | Enum | `getEnumTag` | `unsigned (*)(const T*, M*)` | Read case tag `[0..N-1]` (`HasEnumWitnesses`) |
| 13 | Enum | `destructiveProjectEnumData` | `void (*)(T*, M*)` | Strip tag bits in place to expose payload |
| 14 | Enum | `destructiveInjectEnumTag` | `void (*)(T*, unsigned, M*)` | Fold tag bits into initialized payload |

Slots 8–11 form `TargetTypeLayout` (`ValueWitnessTable.h:290-337`, checked by `static_assert` on `offsetof`). `TargetValueWitnessFlags` (`include/swift/ABI/MetadataValues.h:167-189`) chooses bit polarities so struct composition merges most field flags via bitwise OR:

| Mask | Flag | Semantics / Composition |
| --- | --- | --- |
| `0x000000FF` | `AlignmentMask` | `align - 1` (up to `256`; struct takes `max`) |
| `0x00010000` | `IsNonPOD` | Copy/destroy non-trivial (`memcpy`/noop insufficient) |
| `0x00020000` | `IsNonInline` | `!isBitwiseTakable \|\| size > sizeof(ValueBuffer) \|\| align > alignof(ValueBuffer)` |
| `0x00080000` | `HasSpareBits` | Type has unused spare bits |
| `0x00100000` | `IsNonBitwiseTakable` | Address-sensitive (e.g., side-table weak ref); move != `memcpy` |
| `0x00200000` | `HasEnumWitnesses` | Slots 12–14 present |
| `0x00400000` | `Incomplete` | Dependent/recursive metadata layout not yet finalized |
| `0x00800000` | `IsNonCopyable` | Non-copyable (`~Copyable`) type |
| `0x01000000` | `IsNonBitwiseBorrowable` | Borrow cannot lower as bitwise copy |
| `0x02000000` | `IsAddressableForDependencies` | Address-dependent lifetime tracking |

#### 2.2 Separate `size` vs. `stride`, Tail-Padding Reuse, and Address-Only ABI

Basis: source + documentation + execution

1. **Tail-padding reuse (`Metadata.cpp:2803-2860`, `TypeLayout.rst:19-75`)**: `performBasicLayout` rounds running `size` to each field's `AlignmentMask`, records the offset, and adds `eltLayout->size` (not `stride`). After all fields, `layout.size` stays unpadded while `layout.stride = std::max(size_t(1), roundUp(size, alignMask))` (`Metadata.cpp:2858`). Thus `struct S { x: Int; y: UInt8 }` has `(size=9, align=8, stride=16, offsets=(0, 8))`, and `struct S2 { x: UInt8; s: S; y: UInt8 }` packs `y` into `S`'s tail padding at offset `17` (`size=18, align=8, stride=24, offsets=(0, 8, 17)`), saving `8` bytes over C/Rust `repr(C)` (`size=32`, `y` at offset `24`). Empty structs have `size=0, align=1, stride=1` and take `0` bytes inside structs (`ContainsEmpty { x: Int, y: Empty, z: Int }` has `offsets=(0, 8, 8), size=16`).
2. **3-word `ValueBuffer` and existential containers (`ValueWitnessTable.h:72-83`, `MetadataValues.h:46`, `TypeLayout.rst:276-280`)**: `TargetValueBuffer` holds `NumWords_ValueBuffer = 3` words (`24`B, align `8` on 64-bit). An `OpaqueExistentialContainer` stores values inline iff `canBeInline(isBitwiseTakable, size, align)` holds; Part 1 of `support/verify_layout_algebra_and_witnesses.py` confirms `S2_18B_a8=True`, while `BigPod32_32B_a8`, `Simd16_16B_a16`, and `WeakRef_8B_a8_nonBT` all set `IsNonInline` (`False`).
3. **Indirect calling convention and reabstraction (`ABIStabilityManifesto.md:122-127, 352-370`)**: Opaque generic and resilient values are *address-only* (passed/returned indirectly by pointer). Passing a concrete register-convention function `add1(Int) -> Int` to `apply<T, U>((T) -> U, T) -> U` synthesizes a **reabstraction thunk** bridging register and indirect conventions.

#### 2.3 Single-Payload Enum Composition via Extra Inhabitants

Basis: source + execution

`swift_initEnumMetadataSinglePayload` (`Enum.cpp:173-215`), `getEnumTagCounts` (`Enum.h:28-49`), and `EnumImpl.h:102-190` lay out `Optional<T>` and arbitrary single-payload enums dynamically at runtime:

- When `payload.extraInhabitantCount >= emptyCases`, the enum adds `0` bytes and exports `unusedXI = payloadXI - emptyCases` upward, so `Bool` (`254` XI) $\to$ `Optional<Bool>` (`size=1, XI=253`) $\to$ `Optional<Optional<Bool>>` (`size=1, XI=252`).
- When `emptyCases > payloadXI`, let $k = \text{emptyCases} - \text{payloadXI}$. `getEnumTagCounts(payloadSize, k, 1)` computes `numTags = 1 + (1 if payloadSize >= 4 else ceil(k / 2^(8*payloadSize)))` and maps `numTags` to `0/1/2/4` extra tag bytes appended at `enumAddr + payloadSize`. Part 1 of our probe verifies `301/301` exact tag round-trips on `BigEnum<UInt8>` (`payloadSize=1, emptyCases=300, size=2, numTagBytes=1`) and executes unspecialized `generic_array_reverse` on `Pair<ClassRef, WeakRef>` with `0` ARC leaks and exact weak-reference side-table relocations.

#### 2.4 Library Evolution and Resilience Domains

Basis: documentation + normative

Under Swift Library Evolution (`docs/LibraryEvolution.rst:174-580`, `ABIStabilityManifesto.md:111-120`), public types are resilient (layout-opaque) outside their version-locked **resilience domain**, allowing stored properties to be reordered, added, or turned into computed properties without breaking client binaries (`LibraryEvolution.rst:349-376`). Clients recover monomorphic specialization via explicit opt-ins: **`@frozen`** (locks stored properties permanently, exposing static layout—still *not* C layout, `line 487`), **`@inlinable` + `@usableFromInline`** (publishes body for client specialization, disallowing `private`/`fileprivate` refs and local types; later body edits do not affect already-compiled clients, `lines 174-268`), and **`@_alwaysEmitIntoClient`** (no library ABI symbol at all, `lines 270-286`).

---

### 3. Representation and Levity Polymorphism in GHC

Basis: normative + documentation + source

Eisenberg & Peyton Jones (PLDI '17, pp. 525–539, DOI `10.1145/3062341.3062357`) unified boxed lifted types (`Int`), boxed unlifted types (`Array#`), and unboxed primitives (`Int#`, `Double#`, unboxed tuples/sums, SIMD vectors) in GHC without full monomorphization or Swift-style VWTs.

#### 3.1 `TYPE (r :: RuntimeRep)` and the `BoxedRep Levity` Refinement

Basis: source + documentation

In `ghc/ghc@83038fbee5efea8e3ebd5090b2ff5537462e169d` (`libraries/ghc-internal/src/GHC/Internal/Types.hs:785-815`, `docs/users_guide/exts/representation_polymorphism.rst:12-51`), inhabited types have kind `TYPE r` (`r :: RuntimeRep`):

```haskell
data Levity = Lifted | Unlifted
data RuntimeRep
  = VecRep VecCount VecElem | TupleRep [RuntimeRep] | SumRep [RuntimeRep]
  | BoxedRep Levity
  | IntRep | Int8Rep | Int16Rep | Int32Rep | Int64Rep
  | WordRep | Word8Rep | Word16Rep | Word32Rep | Word64Rep
  | AddrRep | FloatRep | DoubleRep
type LiftedRep = BoxedRep Lifted
type Type      = TYPE LiftedRep
```

Factoring `Levity` inside `BoxedRep Levity` (refining PLDI '17's separate `LiftedRep`/`UnliftedRep` constructors) decouples pointer representation from laziness ($\bot$), enabling levity-polymorphic datatypes (`UnliftedDatatypes`) while keeping unboxed register representations indexed by `RuntimeRep`.

#### 3.2 Binding- and Argument-Position Invariants (`hasFixedRuntimeRep`)

Basis: source + normative

Because GHC neither monomorphizes all generics nor emits runtime VWTs, codegen enforces two invariants (`compiler/GHC/Tc/Utils/Concrete.hs:130-146`, `Note [Representation polymorphism checking]`):

- **I1**: No bound term-level variable may have a representation-polymorphic type.
- **I2**: No function argument may have a representation-polymorphic type.

Thus `bad :: forall r1 r2 (a :: TYPE r1) (b :: TYPE r2). (a -> b) -> a -> b; bad f x = f x` is rejected (unknown register width/class for `x`), whereas `good :: forall r (a :: Type) (b :: TYPE r). (a -> b) -> a -> b; good f x = f x`, eta-reduced `($) f = f` (with stricter evaluation), and bottoms `undefined`/`error :: ... => a` are accepted (`representation_polymorphism.rst:54-121`). GHC enforces `I1`/`I2` via `ConcreteTv` equality constraints `co :: ty ~# concrete_ty` (`Concrete.hs:52-200`), where concrete types are built from concrete `TyCon`s (excluding type/data families). `Note [Fixed RuntimeRep]` (`Concrete.hs:101-109`) notes that requiring a fixed `RuntimeRep` is slightly stricter than necessary for `TYPE (BoxedRep l)`, where pointer representation is already known.

**Duality with Swift**: GHC rejects representation-opaque binders statically to preserve direct register calling conventions; Swift permits arbitrary opaque binders and fields by inserting an address-only indirection and VWT barrier.

---

### 4. Polymorphic Compile-Time Layout Algebras and Non-Injective Fat-Pointer Metadata

Basis: normative + source + execution + derived

Zero-copy systems libraries (`google/zerocopy`, drivers, wire parsers) must verify byte-level invariants polymorphically: padding freedom (`IntoBytes`), alignment domination, niche validity, and exact size-to-metadata bijection for DSTs. Exposing layout only as monomorphic post-instantiation queries breaks modularity across four fronts.

#### 4.1 Monomorphic Layout Walls in Rust Derive Macros

Basis: source + documentation

In `google/zerocopy@ec133ce4d7993775413d852f91c9e3eb2a2a0897`:

1. **Generic `IntoBytes` blocked**: `zerocopy-derive/src/derive/into_bytes.rs:89-181` emits `PaddingFree<Self, PADDING_BYTES>` / `DynamicPaddingFree<Self, HAS_PADDING>` (`zerocopy/src/util/macro_util.rs:53-82`) **only when `ctx.ast.generics.params.is_empty()`** (`line 124`). With *any* generic parameter, derive falls back to: (a) `#[repr(transparent)]` or `#[repr(packed(1))]` (`lines 99-118`), (b) a syntactic homogeneous-field proof (`homogeneous_field_bounds`, `lines 24-87, 145-165`) requiring un-deduplicated `FieldElem: Identity<Type = T>` where-bounds purely to guard against token-hygiene collisions, or (c) requiring every field to be `Unaligned` (`lines 166-175`), rejecting valid generic structs like `#[repr(C)] struct Pair<T, U>(T, U)` even when `T = U = u32`.
2. **Generic unions rejected**: `derive_into_bytes_union` rejects all generic unions (`lines 235-241`).
3. **Nightly `size_of_val_raw` dependence**: Computing trailing-slice offsets without re-implementing `rustc` layout requires unstable `core::mem::size_of_val_raw` on zero-length dangling pointers (`macro_util.rs:22-25, 136-160`).

#### 4.2 Pointer Metadata Abstraction (RFC 2580 and `core::ptr::Pointee`)

Basis: normative + source

RFC 2580 (`rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `text/2580-ptr-meta.md`) and `rust-lang/rust@b0b600668bb9b4a897e2299b0a44289d42276545` (`library/core/src/ptr/metadata.rs:56-212`) expose fat-pointer metadata via:

```rust
#[lang = "pointee_trait"]
#[rustc_deny_explicit_impl]
#[rustc_dyn_incompatible_trait]
pub trait Pointee: PointeeSized {
    #[lang = "metadata_type"]
    type Metadata: fmt::Debug + Copy + Send + Sync + Ord + Hash + Unpin + Freeze;
}
pub trait Thin = Pointee<Metadata = ()> + PointeeSized;
pub const fn metadata<T: PointeeSized>(ptr: *const T) -> <T as Pointee>::Metadata;
pub const fn from_raw_parts<T: PointeeSized>(
    data_pointer: *const impl Thin, metadata: <T as Pointee>::Metadata
) -> *const T;
```

Three limits observed in `metadata.rs`: (1) `Pointee` is closed (`#[rustc_deny_explicit_impl]`, custom DSTs excluded by RFC 2580 `lines 16-17`); (2) `DynMetadata::size_of(self)` returns only the `dyn` tail's size, not the total size of `(i32, dyn Send)` (`lines 191-196`), and slice `Metadata = usize` gives element count $n$ rather than byte size $S(n)$ or its inverse; (3) `DynMetadata` uses special-cased `FieldsShape::Primitive` inside wide pointers vs. `Aggregate` standalone (`lines 174-186`) and non-canonical vtable pointer equality across CGUs (`lines 155-158`).

#### 4.3 Affine-Ceiling Slice-DST Layout Algebra: Closure, Injectivity, and Postmortems

Basis: source + execution + derived

In `google/zerocopy@ec133ce4d7993775413d852f91c9e3eb2a2a0897` (`zerocopy/src/layout.rs:34-207`), nested `#[repr(C)]`/`packed(p)`/`align(m)` slice DSTs normalize into the four-word `TrailingSliceLayout`:

```text
TrailingSliceLayout {
    offset: usize,                                       // physical byte offset of trailing slice start
    elem_size: usize,                                    // E = size_of::<Elem>()
    size_base: usize,                                    // C = fixed bytes outside final rounding
    size_rounding_align_and_phase: RoundingAlignAndPhase // NonZeroUsize encoding A | r (0 <= r < A)
}
```

`RoundingAlignAndPhase` (`layout.rs:52-148`) packs power-of-two $A$ and phase $r \in [0, A)$ as $A \mid r = A + r$, decoding $A = 1 \ll ((\text{BITS} - 1) - \text{leading\_zeros})$ and $r = \text{encoded} \oplus A$. For $n \in \mathbb{N}$ trailing elements:

$$S(n) = C + \mathrm{round\_up}(r + nE, A) = C + \left\lceil \frac{r + nE}{A} \right\rceil A$$

and trailing padding $P(n) = S(n) - (\mathrm{offset} + nE) = (C + r - \mathrm{offset}) + \mathrm{padding\_needed\_for}(r + (nE \bmod A), A)$ is periodic modulo $A$ (`layout.rs:360-415`).

**Theorem 1 (Exact Algebraic Closure Under Nesting)**. *For powers of two $a, A$, integers $c, E \ge 0$, and $0 \le r < a$, $\mathrm{round\_up}(c + \mathrm{round\_up}(r + nE, a), A)$ collapses identically to $C' + \mathrm{round\_up}(r' + nE, A')$ with $A' = \max(a, A)$ and $0 \le r' < A'$:*

1. **$a < A$** (`layout.rs:1432-1472`): Since $a \mid A$, $\mathrm{round\_up}(z, A) = \mathrm{round\_up}(\mathrm{round\_up}(z, a), A)$. As $m = \mathrm{round\_up}(r + nE, a)$ is a multiple of $a$, $\mathrm{round\_up}(c + m, a) = \mathrm{round\_up}(c, a) + m$, so $\mathrm{round\_up}(c + m, A) = \mathrm{round\_up}(\mathrm{round\_up}(c, a) + r + nE, A)$. Setting $F = \mathrm{round\_up}(c, a) + r$, $C' = \mathrm{round\_down}(F, A)$, $r' = F \bmod A$ gives $C' + \mathrm{round\_up}(r' + nE, A)$.
2. **$a \ge A$** (`layout.rs:1473-1486`): Since $A \mid a$, $\mathrm{round\_up}(r + nE, a)$ is already a multiple of $A$, giving $\mathrm{round\_up}(c, A) + \mathrm{round\_up}(r + nE, a)$ with $C' = \mathrm{round\_up}(c, A), A' = a, r' = r$.

Consequently, wrapping a naturally align-$a$ inner slice DST inside `#[repr(C, packed(p))]` with $p < a$ yields `size_align` $= a > \mathrm{align}(\text{outer})$ and `size_phase` $\neq \mathrm{offset} \bmod a$ (`layout.rs:196-205`). Part 2 of `support/verify_layout_algebra_and_witnesses.py` exhaustively verifies Theorem 1 across `38,060` $(a, A, r, c, E)$ configurations over $n \in [0, 23]$.

**Theorem 2 (Exact Injectivity Criterion)**. *Over $n \in \mathbb{N}$, $S(n) = C + \lceil (r + nE)/A \rceil A$ ($A \ge 1, 0 \le r < A, E \ge 0$) is injective if and only if $E \ge A$.*

*Proof*: For $E = 0$, $S$ is constant (rejected by `try_to_nonzero_elem_size`, `layout.rs:796-824, 1743-1746`). For $E \ge A$, $(r + (n+1)E) - (r + nE) = E \ge A \implies S(n+1) \ge S(n) + A > S(n)$ (strictly increasing). For $0 < E < A$, let $f(n) = \lceil (r + nE)/A \rceil$; then
$$\sum_{n=0}^{A-1} \big(f(n+1) - f(n)\big) = f(A) - f(0) = \left\lceil \frac{r + AE}{A} \right\rceil - \left\lceil \frac{r}{A} \right\rceil = E < A.$$
By the Pigeonhole Principle over the $A$ nonnegative integer increments, at least $A - E \ge 1$ indices in $\{0, \dots, A-1\}$ satisfy $f(n+1) = f(n)$, creating adjacent plateaus $S(n) = S(n+1)$. $\square$

Part 2 of our probe verifies Theorem 2 across all `713` `(A, r, E)` triples ($A \in \{1,2,4,8,16\}$) and cross-checks `zerocopy`'s $O(1)$ bit-mask `validate_cast_and_convert_metadata` (`layout.rs:1705-1852`) against brute force across `1,176` `(addr, len, cast_type)` cases.

**Production Soundness Postmortems (`google/zerocopy`)**:

1. **Plateau Metadata-Inversion OOB Slice (`12f746d2307c30455db1875b9b80e45ada5b8675`)**: Previously, `Ref<B, T: ?Sized>(B, PhantomData<T>)` validated an explicit element count $n$ in `from_bytes_with_elems`, discarded $n$, and later inverted `bytes.len()` via `validate_cast_and_convert_metadata` (which returns the *maximum* fitting count). For `#[repr(C)] struct Align4Tail { hdr: u32, tail: [u8] }` (`offset=4, E=1, C=4, A=4, r=0`), $S(0..5) = [4, 8, 8, 8, 8, 12]$: a `Ref` constructed with `elems = 1` on an 8-byte buffer reconstructed `elems = 4`, reading 3 unvalidated trailing-padding bytes as slice elements (`Header3 { hdr: u16, tag: u8, tail: [u8] }` at `align(4)` similarly collides $n=0$ and $n=1$ at `4`B). Fix: `zerocopy/src/ref.rs` stores `elem_count: usize` in `Ref` under the invariant `T::size_for_metadata(from_elem_count(elem_count)) == Some(referent.len())`.
2. **Nested Packed-Around-Aligned Size Understatement (`242ff08b5cf0d7723c0bc29ccfac0628b967d794`)**: Wrapping a naturally aligned `#[repr(C)] struct Inner { a: u32, b: u8, s: [u8] }` (`align=4, offset=5, C=4, A=4, r=1`) inside a compiler-accepted `#[repr(C, packed(2))] struct Outer { hdr: u8, inner: Inner }` (legal because `Inner` has natural alignment `4`, not `#[repr(align(4))]`) yields `Outer` with `align=2, offset=7, C=6, A=4, r=1` and exact sizes $S(0..6) = [10, 10, 10, 10, 14, 14, 14]$. Naive flattening $\mathrm{round\_up}(7 + n, 2)$ computes $[8, 8, 10, 10, 12, 12, 14]$, understating object size by `2` bytes at $n \in \{0, 1, 4, 5\}$. Fix: commit `242ff08b5cf0d7723c0bc29ccfac0628b967d794` adopted the closed four-word `TrailingSliceLayout` and Kani-verified every transition.

#### 4.4 Decidable Polymorphic Padding Constraint Algebras

Basis: derived + execution + normative

Equipping generic parameters $T$ with symbolic layout attributes $(\mathrm{Align}(T), \mathrm{Size}(T), \mathrm{NoPad}(T))$ under Rust/C's `Sized` axioms ($\mathrm{Align}(T) = 2^{k_T}$ and $\mathrm{Align}(T) \mid \mathrm{Size}(T)$, including aligned ZSTs with $\mathrm{Size}(T) = 0$) reduces universal interior- and trailing-padding freedom over `repr(C)`/`packed(P)`/`align(M)` structs to a decidable small-model problem over power-of-two alignments and size residues modulo maximum alignment. Part 3 of `support/verify_layout_algebra_and_witnesses.py` decides seven representative generic schemas:

| Generic Struct (`#[repr(C, ...)]`) | Constraint | Universally Padding-Free? | Witness / Proof |
| --- | --- | --- | --- |
| `Pair<T, U>(T, U)` | None | **No** | `T=(1,1), U=(0,2)` (`[u16; 0]`): `1`B interior pad (non-ZST `U=(2,2)`: `1`B interior + `1`B trailing) |
| `Homog<T>(T, [T; 3], [T])` | None (or `packed(P)`) | **Yes** | $b = \min(\mathrm{Align}(T), P) \mid \mathrm{Align}(T) \mid \mathrm{Size}(T)$ keeps every offset aligned to $b$ |
| `Pair<T, U>(T, U)` | `Align(T) >= Align(U)` | **No** | Interior pad `0`, **trailing pad `1`B** at `T=(0,2), U=(1,1)` and non-ZST `T=(2,2), U=(1,1)` |
| `Pair<T, U>(T, U)` | `Align(T) >= Align(U) ∧ Align(T) \| Size(U)` | **Yes** | Offset after `T` divisible by `Align(U)`; total size divisible by `Align(T)` |
| `#[repr(C, packed(2))] Pack2<T>(u16, T)` | None | **No** | Interior pad `0`, **trailing pad `1`B** at `T=(1,1)` |
| `#[repr(C, packed(2))] Pack2<T>(u16, T)` | `2 \| Size(T)` | **Yes** | `2 + Size(T)` divisible by `struct_align = 2` |
| `#[repr(C, packed(1))] Pack1<T, U>(u8, T, U)` | None | **Yes** | Effective field and struct alignment is `1` |

Two structural lessons emerge directly from the solver: (1) **aligned ZSTs** (`[u16; 0]`, `rust-lang/reference/src/type-layout.md:22`) introduce both interior and trailing padding and must belong to any sound constraint solver's domain; (2) **non-increasing field alignment** prevents *inter-field* padding in `repr(C)` but never prevents *trailing* padding without a modular divisibility constraint $\mathrm{Align}(T_0) \mid \sum_{i \ge 1} \mathrm{Size}(T_i)$.

---

### 5. Reference-Admissible Nondeterministic Layout Specifications

Basis: normative + documentation + execution + derived

In `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`src/type-layout.md:8, 169-228`), `#[repr(Rust)]` guarantees **only**: (1) `offset(f) % align(f) == 0`, (2) `align(S) >= max(align(f))`, (3) non-overlapping fields in some order (`r[layout.repr.rust.struct]`), (4) zero size for all-ZST structs, zero-variant enums, and single-variant all-ZST enums, and (5) `size % align == 0`—with *"no other guarantees of data layout"* (`r[layout.repr.rust.unspecified]`).

#### 5.1 Bounded Demonic Nondeterminism vs. Concrete Compiler Refinement

Basis: derived + execution + normative

To separate portable guarantees from compiler-version coincidences (cf. `anneal-forward-compatible-mir-semantics-and-reference-admissible-refinement` and `rustc-layout-computation-target-datalayouts-and-parametricity`), model the normative spec for type $T$ on target $\tau$ as its set of reference-admissible layouts $\mathcal{A}_{\mathrm{Ref}}(T, \tau)$:

- A **portable proof** establishes $\forall L \in \mathcal{A}_{\mathrm{Ref}}(T, \tau).\; \Phi(T, L)$ (demonic nondeterminism). Any conforming compiler version $C_v$ is a deterministic downward refinement picking $L_{C_v}(T, \tau) \in \mathcal{A}_{\mathrm{Ref}}(T, \tau)$, so portable proofs transport automatically across upgrades.
- **Concrete separation** (Part 4 of `support/verify_layout_algebra_and_witnesses.py`): For `#[repr(Rust)] struct R { a: u8, b: u16, c: u8 }`, $\mathcal{A}_{\mathrm{Ref}}(R)$ includes both greedy-packed order `(b, a, c)` (`size=4, padding=0`) and declaration order `(a, b, c)` (`size=6, padding=2`), plus over-padded layouts. Non-overlap and field alignment hold across `12/12` enumerated admissible layouts, whereas `size == 4` and zero padding hold *existentially* (`True`) yet fail *demonically* (`False`). Adding `#[repr(C)]` or `#[repr(packed(1))]` collapses $\mathcal{A}_{\mathrm{Ref}}(T, \tau)$ to a deterministic singleton (modulo target primitive alignments).

#### 5.2 Unifying ABI Resilience, Layout Algebras, and Verified Specialization

Basis: derived

Combining Sections 1–5 points to a unified compiler/verifier architecture: (1) assign every generic definition a canonical **witness-passing reference semantics** (generalizing Swift's `TargetTypeLayout`/VWT and `DstLayout`) for separate checking, zero PMEs, and cross-DSO stability; (2) lift **decidable layout constraints** (`Align`, `NoInteriorPadding`, `NoTrailingPadding`, modular `Size` divisibility, and `E >= A` DST injectivity) into function/trait signatures; and (3) treat **monomorphization and `repr(Rust)` layout fixing** as certified refinements permitted inside version-locked resilience domains, falling back cleanly to the resilient witness path across independent binary boundaries.

---

## Boundaries

- **not examined**:
  - Empirical throughput/binary-size benchmarks comparing Swift resilient vs. `@inlinable`/`@frozen` builds or Go 1.18+ dictionary overhead on production workloads.
  - Swift multi-payload enum spare-bit scattering (`swift_initEnumMetadataMultiPayload`) and Objective-C tagged-pointer/ISA-masking paths beyond single-payload VWTs.
  - JVM Project Valhalla specialized generics, OCaml 5 / OxCaml unboxed layouts, C++20 modules / `[[no_unique_address]]`, and draft Rust `crABI` proposals.
  - Internal `rustc` `LayoutCalculator` heuristics and LLVM `DataLayout` lowering (see `rustc-layout-computation-target-datalayouts-and-parametricity`).
- **unknown**:
  - Whether upstream Rust will adopt a first-class polymorphic layout constraint algebra, stabilize `generic_const_exprs` / `ptr_metadata` / `size_of_val_raw`, or add user-defined custom DSTs.
  - Whether Swift will stabilize register-splitting calling conventions for partially-opaque aggregates (`ABIStabilityManifesto.md:354`).
- **known not to apply**:
  - Swift's distinct `size` vs. `stride` tail-padding reuse (`TypeLayout.rst:42-49`) does **not** apply to C or Rust `#[repr(C)]` structs (`size == stride`).
  - The four-word affine-ceiling algebra $S(n) = C + \mathrm{round\_up}(r + nE, A)$ applies strictly to `repr(C)`/`packed`/`align` slice-tail DSTs, not `dyn Trait`, `extern` types, or `repr(Rust)` DSTs.
  - Shallow outer padding-freedom (`NoInteriorPadding` of field offsets) does **not** imply recursive padding-freedom of generic fields `T` without an explicit field bound (`IntoBytes`).
  - GHC's `hasFixedRuntimeRep` restriction does **not** forbid representation-polymorphic return types or eta-reduced combinators (`($) f = f`), only term binders and function arguments.
- **unsupported**:
  - Cross-DSO generic instantiation and assembly-implemented generics in Go's static-dictionary GCShape model (`generics-implementation-gcshape.md:37`) and Rust monomorphization.
  - Non-monomorphisable polymorphic recursion generating unbounded distinct types in Rust and Go (`generics-implementation-dictionaries-go1.18.md:62-64`).
  - Representation-polymorphic term binders, function arguments, or datatype fields in GHC (`Concrete.hs:130-165`).
  - Combining `#[repr(align(N))]` and `#[repr(packed(M))]` on one Rust type, or nesting an `#[repr(align(N))]` type inside a `#[repr(packed(M))]` type (`rust-lang/reference/src/type-layout.md:653-654`).

---

## Evidence

Verified on `2026-11-19`:

### Primary Source Repositories (Exact 40-Char Commits)

1. **`swiftlang/swift`** @ `3be0cf4b450b5366cff4b1a7e5bf7e5b4633224f`:
   - `include/swift/ABI/ValueWitness.def:97-294`; `ValueWitnessTable.h:72-83, 132-239, 245-337`; `MetadataValues.h:46, 167-241`; `Metadata.h:160-214, 265-286, 379-413`; `Enum.h:28-49`.
   - `stdlib/public/runtime/Metadata.cpp:2803-2860` (`performBasicLayout`); `Enum.cpp:85, 173-215`; `EnumImpl.h:102-190`.
   - `docs/ABI/TypeLayout.rst:19-75, 109-302`; `docs/ABIStabilityManifesto.md:67-375`; `docs/LibraryEvolution.rst:174-580`.
2. **`ghc/ghc`** @ `83038fbee5efea8e3ebd5090b2ff5537462e169d`:
   - `libraries/ghc-internal/src/GHC/Internal/Types.hs:785-815`; `compiler/GHC/Tc/Utils/Concrete.hs:52-200`; `docs/users_guide/exts/representation_polymorphism.rst:1-187`.
3. **`google/zerocopy`** @ `ec133ce4d7993775413d852f91c9e3eb2a2a0897`, `12f746d2307c30455db1875b9b80e45ada5b8675`, `242ff08b5cf0d7723c0bc29ccfac0628b967d794`:
   - `zerocopy/src/layout.rs:34-207, 252-491, 565-775, 1231-1853`; `zerocopy/zerocopy-derive/src/derive/into_bytes.rs:24-259`; `zerocopy/src/util/macro_util.rs:22-160`; `zerocopy/src/ref.rs` (in `12f746d2307c30455db1875b9b80e45ada5b8675`).
4. **`rust-lang/rfcs`** @ `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`: `text/2580-ptr-meta.md:1-397`.
5. **`rust-lang/rust`** @ `b0b600668bb9b4a897e2299b0a44289d42276545`: `library/core/src/ptr/metadata.rs:1-268`; `compiler/rustc_monomorphize/src/lib.rs:1-57`.
6. **`rust-lang/reference`** @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`: `src/type-layout.md:1-727`.
7. **`golang/proposal`** @ `83ee2aaf9fdcc1a1cf4bb4d20216fc979635cf04`: `design/generics-implementation-gcshape.md:1-239`, `design/generics-implementation-dictionaries-go1.18.md:1-133`.
8. **`dotnet/runtime`** @ `db341b0b461356d954079d27e86cb47c929e7e8a`: `src/coreclr/vm/genericdict.h:1-95`, `generics.h:158-168`, `docs/design/coreclr/botr/type-system.md:156-245`.

### Peer-Reviewed Literature

- Robert Harper & Greg Morrisett. *Compiling Polymorphism Using Intensional Type Analysis*. POPL '95, pp. 130–141, 1995. DOI: `10.1145/199448.199475`.
- David Tarditi, Greg Morrisett, Perry Cheng, Christopher Stone, Robert Harper, & Peter Lee. *TIL: A Type-Directed Optimizing Compiler for ML*. PLDI '96, pp. 181–192, 1996. DOI: `10.1145/235805.235830`.
- Andrew Kennedy & Don Syme. *Design and Implementation of Generics for the .NET Common Language Runtime*. PLDI '01, pp. 1–12, 2001. DOI: `10.1145/378795.378797`.
- Richard A. Eisenberg & Simon Peyton Jones. *Levity Polymorphism*. PLDI '17, pp. 525–539, 2017. DOI: `10.1145/3062341.3062357`.

### Preserved Executable Verification Probe

```console
python3 -B support/verify_layout_algebra_and_witnesses.py
```

Observed output (`exit 0`, `2026-11-19`):

```text
[PASS] Part 1 (Swift Value Witness Table composition & generic execution): {'S_layout': (9, 8, 16, (0, 8)), 'S2_layout': (18, 8, 24, (0, 8, 17)), 'S2_c_size': 32, 'Optional_Optional_Bool': (1, 1, 252), 'BigEnum_300_cases_roundtrip': '301/301 exact', 'Pair_ClassRef_WeakRef_inline': False, 'ValueBuffer_inline_flags': {'S2_18B_a8': True, 'BigPod32_32B_a8': False, 'Simd16_16B_a16': False, 'WeakRef_8B_a8_nonBT': False}}
[PASS] Part 2 (Affine-ceiling slice-DST algebra & plateau counterexamples): {'closure_identities_checked': 38060, 'injectivity_triples_checked': 713, 'cast_oracle_checks': 1176, 'align4_tail_sizes_0_to_5': [4, 8, 8, 8, 8, 12], 'outer_packed2_inner_align4_exact': [10, 10, 10, 10, 14, 14, 14], 'outer_packed2_inner_align4_naive_bug': [8, 8, 10, 10, 12, 12, 14]}
[PASS] Part 3 (Symbolic polymorphic interior/trailing padding solver): {'Pair_unconstrained': (False, {'T': ConcreteParamVal(size=1, align=1), 'U': ConcreteParamVal(size=0, align=2)}, (1, 0)), 'Homog_slice_dst': True, 'Homog_packed4': True, 'Pair_alignT_ge_alignU': (False, {'T': ConcreteParamVal(size=0, align=2), 'U': ConcreteParamVal(size=1, align=1)}, (0, 1)), 'Pair_alignT_ge_alignU_nonzero': (False, {'T': ConcreteParamVal(size=2, align=2), 'U': ConcreteParamVal(size=1, align=1)}, (0, 1)), 'Pair_alignT_ge_alignU_and_sizeU_div_alignT': True, 'Pack2_u16_T_unconstrained': (False, {'T': ConcreteParamVal(size=1, align=1)}, (0, 1)), 'Pack2_u16_T_even_size': True, 'Pack1_u8_T_U': True}
[PASS] Part 4 (Reference-admissible repr(Rust) nondeterministic refinement): {'struct_R_fields': [('a', 1, 1), ('b', 2, 2), ('c', 1, 1)], 'admissible_layouts_enumerated': 12, 'compact_sizes': [4, 6], 'demonic_zero_padding_holds': False, 'existential_zero_padding_holds': True}
```

---

## Revalidation

1. **Executable algebraic & VWT probe**: Run `python3 -B support/verify_layout_algebra_and_witnesses.py` (expected exit `0`, <2s) to re-verify Swift VWT composition, affine-ceiling closure (`38,060` cases), injectivity iff $E \ge A$ (`713` triples), `zerocopy` counterexamples, polymorphic padding decisions, and `repr(Rust)` nondeterminism.
2. **Swift ABI drift**: Diff `ValueWitness.def`, `MetadataValues.h` (`TargetValueWitnessFlags`, `NumWords_ValueBuffer`), `Enum.h` (`getEnumTagCounts`), and `Metadata.cpp` (`performBasicLayout`) against `3be0cf4b450b5366cff4b1a7e5bf7e5b4633224f` for newly allocated flag bits or calling-convention changes.
3. **GHC representation polymorphism**: Diff `GHC/Internal/Types.hs` (`RuntimeRep`, `Levity`) and `GHC/Tc/Utils/Concrete.hs` (`Note [Fixed RuntimeRep]`) against `83038fbee5efea8e3ebd5090b2ff5537462e169d` to detect relaxation for `BoxedRep l` binders or new `RuntimeRep` constructors.
4. **Rust / `zerocopy` drift**: Diff `zerocopy/src/layout.rs` and `into_bytes.rs` against `ec133ce4d7993775413d852f91c9e3eb2a2a0897`; check `library/core/src/ptr/metadata.rs` against `b0b600668bb9b4a897e2299b0a44289d42276545` for `ptr_metadata` / `size_of_val_raw` stabilization; diff `rust-lang/reference/src/type-layout.md` against `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`.
5. **Go / .NET generics drift**: Check `dotnet/runtime` `src/coreclr/vm/genericdict.h` and Go's `src/cmd/compile/internal/noder/` for GCShape or dictionary changes.
