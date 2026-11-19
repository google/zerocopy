# CLR Reified Generics and Interior Pointers, Swift Value Witness Tables and CoW ARC, and Julia World-Age Multiple Dispatch

## Summary

Modern industrial runtimes beyond the JVM adopt three fundamentally distinct solutions to the joint problem of **polymorphic value layout, memory safety across managed/native boundaries, and dynamic compilation**:

1. **.NET CLR (`dotnet/runtime` `fcb04a83f3013e65d573dc0ec240c7a5a720db3a`) — Hybrid Reified Generics, Stack-Confined Interior Pointers, and Zero-Init/Tearing Boundaries**:
   - CoreCLR preserves exact generic type arguments at runtime, sharing a single JIT body across reference-type instantiations via canonical `__Canon` substitution (`ClassLoader::CanonicalizeGenericArg`) + per-instantiation lookup dictionaries (`DictionaryLayout`), while **fully specializing value-type instantiations** to avoid boxing.
   - `Span<T>` embeds a GC-tracked interior pointer (`internal readonly ref T _reference; private readonly int _length;`) and is marked `IsByRefLike` (`ref struct`), enforced at class-load time (`methodtablebuilder.cpp`) to prohibit heap/static storage, boxing, or array elements—simultaneously ensuring GC compaction tracks stack interior pointers and **preventing multi-threaded 16-byte struct tearing from pairing a small array pointer with a large length**. Generic parameters can opt into `ref struct` arguments via `gpAllowByRefLike = 0x0020` (`allows ref struct`).
   - Every CLR `struct` admits an implicit all-zero `default(T)` state (forcing null-initialization guards such as `ImmutableArray<T>.ThrowNullRefIfNotInitialized()`), and multi-word heap structs exceeding pointer width (`IntPtr.Size`) tear under data races. `Memory<T>` remains memory-safe under tearing only because `Memory<T>.Span` defensively snapshots `_object`, reads the underlying object's real length, and re-validates bounds (`ArgumentOutOfRangeException`), converting potential out-of-bounds memory corruption into either an exception or a logically wrong in-bounds slice.
2. **Swift (`swiftlang/swift` `e96891912c1fbf1174f4faf3f63a9d4deb04e39f`) — Unmonomorphized Layout Polymorphism via Value Witness Tables, CoW ARC Uniqueness, and Objective-C Interop**:
   - Swift achieves separate-compilation ABI stability (Library Evolution) and unspecialized generic compilation without boxing or monomorphization by passing `Metadata*` pointers whose **offset `-1` word** points to a **Value Witness Table (VWT)** (`ValueWitness.def`) supplying dynamic lifecycle hooks (`initializeWithCopy`, `initializeWithTake`, `destroy`, `getEnumTagSinglePayload`, etc.) and layout data (`size`, `stride`, `flags`, `extraInhabitantCount`), plus dynamic struct field-offset vectors.
   - Existential containers pack values inline in a 3-word `ValueBuffer` (`NumWords_ValueBuffer = 3`, 24 bytes on 64-bit) iff `size <= 24`, alignment fits, and `!IsNonBitwiseTakable`; larger or weak-reference-bearing structs set `IsNonInline` and heap-box. Extra inhabitants allow `Optional<T>` to compress `.none` into 0 extra bytes polymorphically.
   - Swift value-type Copy-on-Write (`Array`, `Dictionary`, `String`) tests strong uniqueness via `InlineRefCountBits::isUniquelyReferenced()` (`!UseSlowRC && !IsDeiniting && StrongExtraRefCount == 0`, following the weak side table if present) and brackets buffer mutations with `Builtin.beginCOWMutation` / `endCOWMutation`. Weak and unowned references do **not** break CoW uniqueness; however, Objective-C-bridged objects always fail `swift_isUniquelyReferencedNonObjC_nonNull` (`usesNativeSwiftReferenceCounting_nonNull`), forcing defensive $O(N)$ copies across the `objc_msgSend` interop boundary.
3. **Julia (`JuliaLang/julia` `6478933d4232a63baa7286faf5182a8521f6fb05`) — Symmetric Open Multiple Dispatch and Monotonic World-Age JIT Epoch Isolation**:
   - Julia's type system combines invariant parametric nominal types (`Vector{Int64} <: Vector{Real}` is `false`), covariant `Tuple`s, bounded existential `UnionAll` types, and the **diagonal rule** (`src/subtype.c`: a `UnionAll` variable occurring covariantly $\ge 2$ times and never invariantly ranges over concrete types only, so `Tuple{Real, Real} <: Tuple{T, T} where T<:Real` is `false`). Symmetric open dispatch resolves specificity across all arguments (`jl_type_morespecific`) and defers overlapping method ambiguities to runtime `MethodError`.
   - To permit aggressive JIT specialization, devirtualization, and inlining in the presence of dynamic `eval` without on-stack replacement (OSR), every method insertion atomically advances the global `jl_world_counter` (`jl_method_table_insert`), stamps `method->primary_world`, and clamps conflicting cached `jl_code_instance_t` intervals (`max_world = new_world - 1`) via backedge traversal. Each task executes at a fixed `ct->world_age`, isolating running frames from newly `eval`-ed methods (`MethodError: ... too new`) unless code explicitly crosses the epoch boundary with `Core.invokelatest` (`jl_f_invokelatest`) or `invoke_in_world`.

## Applicability

This report synthesizes and compares three independent production runtimes inspected directly at pinned upstream commits:

- **.NET CoreCLR and Base Class Library**: `dotnet/runtime` commit `fcb04a83f3013e65d573dc0ec240c7a5a720db3a` (`main`), interpreted alongside ECMA-335 (6th Edition, June 2012), CoreCLR's authoritative runtime memory model (`docs/design/specs/Memory-model.md`), and Kennedy & Syme (PLDI 2001). Applies to modern .NET (CoreCLR/.NET 9+ including `gpAllowByRefLike` / C# 13 `allows ref struct` and `ref` fields in `Span<T>`); older .NET Framework 4.x lacked `ref` fields (using `ByReference<T>` intrinsic hacks) and lacked `gpAllowByRefLike`.
- **Swift Compiler, Runtime, and Standard Library**: `swiftlang/swift` commit `e96891912c1fbf1174f4faf3f63a9d4deb04e39f` (`main`), covering Swift ABI-stable platforms (Apple Darwin with `SWIFT_OBJC_INTEROP = 1`, where class metadata `kind` is an Objective-C `isa` pointer `> 2047`) and non-ObjC platforms (Linux/Windows, where `SWIFT_OBJC_INTEROP = 0` and class metadata `kind == 0`). Notes explicitly where Apple ObjC interop behavior diverges from non-Darwin targets.
- **Julia Runtime and Type System**: `JuliaLang/julia` commit `6478933d4232a63baa7286faf5182a8521f6fb05` (`master`), interpreted alongside Zappa Nardelli et al. (OOPSLA 2018) and Belyakova et al. (OOPSLA 2020). Note that the pinned `master` revision includes post-1.10 refinements (`jl_f_invoke_in_world`, cached `body_occurs_inv` diagonal-rule tracking in `subtype.c`, and deferred method-table invalidation records in `gf.c`).
- **Execution evidence scope**: Because `.NET`, `swiftc`, and `julia` compiler toolchains were not installed on the observation host, execution evidence consists of self-contained Python formal models directly encoding the exact verified upstream algorithms (`subtype.c` diagonal rule, `gf.c` world-age epoch & backedge invalidation, `ValueWitness.def`/`MetadataValues.h` existential & extra-inhabitant layout, and `Memory.cs` 8-state struct-tearing interleaving enumeration). Native binary execution of those three toolchains is explicitly recorded under **Boundaries** (`not examined`).

## Findings

### 1. .NET CLR Reified Generics: `__Canon` Sharing vs. Value-Type Specialization

**Basis:** normative (ECMA-335 6th Edition) + source (`dotnet/runtime` `src/coreclr/vm/generics.cpp`, `src/coreclr/vm/genericdict.h`) + derived (Kennedy & Syme, PLDI 2001, DOI `10.1145/381694.378797`).

#### Canonical Sharing vs. Value Specialization (`ClassLoader::CanonicalizeGenericArg`)
Unlike Java's erasure (which collapses `List<String>` and `List<Integer>` to raw `List` and forces primitive boxing) and unlike C++/Rust monomorphization (which duplicates code for every concrete type argument), CoreCLR implements **runtime-reified hybrid generics** (`src/coreclr/vm/generics.cpp:27-56`):

```cpp
// dotnet/runtime src/coreclr/vm/generics.cpp:37-52
CorElementType et = thGenericArg.GetSignatureCorElementType();
if (CorTypeInfo::IsObjRef_NoThrow(et))
    return TypeHandle(g_pCanonMethodTableClass);   // __Canon: shared code!
if (et == ELEMENT_TYPE_VALUETYPE) {
    // Don't share structs. Propagate sharability through them
    // (e.g., struct<object> shares with struct<string>).
    return TypeHandle(thGenericArg.GetCanonicalMethodTable());
}
return thGenericArg;
```

This rule partitions all generic instantiations into two compilation regimes:

| Type Argument Class | Canonical Representation | JIT Machine Code | Runtime Type Identity | Primary Trade-Off |
| :--- | :--- | :--- | :--- | :--- |
| Reference types (`string`, `object`, interfaces, arrays) | `System.__Canon` (`g_pCanonMethodTableClass`) | **Single shared body** across all reference instantiations | **Exact** (`typeof(T)` / `MethodTable` preserved via runtime dictionary) | Avoids code bloat; incurs dictionary indirection for `new T()`, `castclass`, `typeof(T)`, static fields, and generic calls. |
| Primitive & non-generic value types (`int`, `double`, `Guid`) | Exact `TypeHandle` (never `__Canon`) | **Dedicated specialized body** per distinct value type | **Exact** (baked directly as JIT constants) | Zero boxing, exact register/stack layout, full devirtualization of constrained calls; risks JIT time & code-size explosion. |
| Generic value types (`KeyValuePair<string, int>`) | `KeyValuePair<__Canon, int>` | Shared across ref-type sub-args, specialized per value sub-arg | **Exact** via recursive canonicalization (`generics.cpp:46-48`) | Balanced sharing when structs wrap references. |

#### Generic Runtime Lookup Dictionaries (`DictionaryLayout`)
Because shared `__Canon` code cannot bake instantiation-specific pointers (e.g., `newobj C<!0>` or `castclass !!0[]`) into native instructions, CoreCLR attaches a lazily populated **`Dictionary`** to every concrete generic `MethodTable` (for generic types) and `InstantiatedMethodDesc` (for generic methods), described by a shared **`DictionaryLayout`** (`src/coreclr/vm/genericdict.h:18-81`):

- **Supported slot kinds (`enum DictionaryEntryKind`, lines 51–64)**: `EmptySlot (0)`, `TypeHandleSlot (1)`, `MethodDescSlot (2)`, `MethodEntrySlot (3)`, `ConstrainedMethodEntrySlot (4)` (devirtualizing `constrained. callvirt` on generic `T`), `DispatchStubAddrSlot (5)`, `FieldDescSlot (6)`, `DeclaringTypeHandleSlot (7)`, and `DeclaringTypeHandleFromMethodSlot (8)`.
- **Hidden context parameter**: Shared generic instance methods recover their exact dictionary from `this->MethodTable`; shared generic static methods and generic instance methods on structs receive an implicit **instantiating stub / hidden `MethodTable*` or `MethodDesc*` context parameter**.
- **Expansion and growth**: Initial generic method dictionaries allocate `NUM_DICTIONARY_SLOTS = 4` (`genericdict.h:93`; `1` in `_DEBUG` builds to stress-test expansion) and dynamically chain expanded tables via a back-pointer slot (`ExpandDictionaryLayout`, lines 125–145).
- **Polymorphic recursion hazard**: Because value-type generics instantiate lazily on demand, polymorphic recursion such as `struct Loop<T> { void f() { new Loop<Loop<T>>().f(); } }` creates an unbounded chain of distinct `MethodTable` layouts; CoreCLR enforces a type-loader recursion bound and throws `TypeLoadException` rather than looping infinitely at load time (first formalized by Kennedy & Syme, PLDI 2001).

---

### 2. CLR `Span<T>`, `ref struct` Interior GC Pointers, and `gpAllowByRefLike`

**Basis:** normative (ECMA-335 `byref` / C# 11–13) + source (`dotnet/runtime` `Span.cs`, `methodtablebuilder.cpp`, `corhdr.h`).

#### `Span<T>` Layout and Managed Interior Pointers (`byref`)
In `src/libraries/System.Private.CoreLib/src/System/Span.cs:28-33`, `Span<T>` is declared:
```csharp
[Intrinsic]
public readonly ref struct Span<T>
{
    internal readonly ref T _reference;  // A byref (managed interior pointer) or native ptr
    private readonly int _length;
}
```
On 64-bit targets, `Span<T>` is a **16-byte** value (8-byte `byref` + 4-byte `int` + 4-byte alignment padding) that uniformly addresses GC heap array interiors (`MemoryMarshal.GetArrayDataReference(array)` + `Unsafe.Add`), stack-allocated memory (`stackalloc`), and unmanaged native buffers (`void*`).

The `_reference` field is a CLR **managed pointer (`ELEMENT_TYPE_BYREF`)**—an interior pointer that may point into the *middle* of a GC-allocated heap object rather than its header. When CoreCLR's compacting garbage collector relocates an array, the JIT's per-frame `GCInfo` tables report every live stack/register `byref` slot so the GC locates the enclosing object header (via brick tables / heap segment metadata) and adjusts `_reference` by the exact relocation delta. Crucially:
- **Heap storage of `byref` is forbidden**: Supporting arbitrary interior pointers inside heap objects would require scanning and relocating interior fields across the entire GC heap and card tables during every collection.
- **Unmanaged `Span(void* pointer, int length)` GC-barrier check (`Span.cs:109-118`)**: Constructing a `Span<T>` over raw unmanaged memory invokes `RuntimeHelpers.IsReferenceOrContainsReferences<T>()` and throws `ArgumentException` if `T` is or contains any GC reference—preventing unmanaged buffers from hiding unscanned object references from the GC.
- **Array covariance guard (`Span.cs:49-50, 78-79`)**: Because CLR reference arrays are covariant (`string[]` is assignable to `object[]`), `Span<T>` constructors explicitly check `if (!typeof(T).IsValueType && array.GetType() != typeof(T[])) ThrowHelper.ThrowArrayTypeMismatchException();`. Without this exact-type check, mutating a `Span<object>` backed by a `string[]` via direct `byref` writes would bypass per-store `stelem.ref` covariance checks and corrupt the `string[]` with arbitrary objects!

#### Runtime `IsByRefLike` Enforcement and the `gpAllowByRefLike` Anti-Constraint
CoreCLR enforces stack-only confinement of `ref struct` types directly inside `MethodTableBuilder` (`src/coreclr/vm/methodtablebuilder.cpp:1400-1408, 1801-1804, 4358-4391`):
- Types carrying `[IsByRefLikeAttribute]` set `pMT->SetIsByRefLike()`.
- Attempting to place any `ByRefLike` type in a **static field** or **instance field of a class or non-`ref` struct** fails class loading with `TypeLoadException` (`BuildMethodTableThrowException(IDS_CLASSLOAD_BYREF_OR_BYREFLIKE_STATICFIELD)`). Boxing (`box`), array creation (`Span<T>[]`), interface implementation (prior to constrained `allows ref struct` dispatch), and capture in async/iterator/lambda heap state machines are likewise rejected.
- **C# 13 / .NET 9 `allows ref struct` (`src/coreclr/inc/corhdr.h:847-853`)**: Historically, no generic type parameter `T` could be instantiated with `Span<U>` because generic code could box `T` or store `T` in a heap field. CoreCLR extended `CorGenericParamAttr` with bit **`gpAllowByRefLike = 0x0020`** (`gpSpecialConstraintMask = 0x003C`). When a generic parameter declares `where T : allows ref struct`, the compiler and verifier prohibit boxing or heap-storing `T` inside that generic definition, unlocking zero-allocation generic abstractions over `Span<T>` without weakening `byref` stack soundness.

---

### 3. CLR Default Zero-Init Invariant Bypass and Multi-Word Struct Tearing

**Basis:** normative (ECMA-335 §I.12.6.6; `dotnet/runtime` `docs/design/specs/Memory-model.md`) + source (`Memory.cs`, `ImmutableArray_1.cs`) + execution (Python 8-state struct-tearing interleaving probe).

#### The Default Zero-Initialization Invariant Bypass
Every CLR value type (`struct`) is implicitly inhabited by its all-zero bit representation `default(T)`—produced by `default`, `new T[n]` array allocation, uninitialized class fields, or `Unsafe.SkipInit` / `initobj` IL—**regardless of whether the struct defines custom constructors or omits a parameterless constructor**. Consequently, no CLR `struct` can enforce a non-zero construction invariant at the type-system level:

- **Core library witness (`ImmutableArray<T>`, `src/libraries/System.Collections.Immutable/src/System/Collections/Immutable/ImmutableArray_1.cs:167-350`)**: `ImmutableArray<T>` is a thin `readonly struct` wrapping a single `internal readonly T[]? array` field. Because callers can always obtain `default(ImmutableArray<T>)` (with `array == null`, distinct from `ImmutableArray<T>.Empty`), virtually every member (`IndexOf`, `LastIndexOf`, `Insert`, `InsertRange`, `Length`, indexing) must defensively begin with `self.ThrowNullRefIfNotInitialized()` (lines 169, 254, 316, 348), turning what appears to be a non-null value collection into a runtime `NullReferenceException` / `InvalidOperationException` hazard whenever an uninitialized struct leaks.

#### .NET Runtime Memory Model vs. ECMA-335 and Struct Tearing
CoreCLR's official memory model (`docs/design/specs/Memory-model.md:4-173`) explicitly documents how the real .NET runtime strengthens ECMA-335 while preserving hardware-width atomicity limits:

- **Strengthenings over ECMA-335**: Prohibits speculative writes and introduced reads (lines 46–59); guarantees **data-dependent read ordering** (lines 118–132: indirect reads through a reference cannot execute before loading the reference); guarantees **release semantics on object reference assignment** (lines 134–146: publishing a freshly constructed object reference commits prior constructor field writes to other threads and background GC, though note `Memory-model.md:146` flags an open compiler compliance audit!).
- **Atomicity ceiling (`Memory-model.md:18-32, 157-160`)**: Ordinary memory reads and writes are atomic **only** for properly aligned primitive types, enums, unmanaged pointers, and managed references with size **$\le$ platform pointer size (`IntPtr.Size`: 4 bytes on 32-bit, 8 bytes on 64-bit)**. Multi-word structs (such as 16-byte `Guid`, `Decimal`, `Memory<T>`, or custom `(T[], int, int)` structs) are copied field-by-field or word-by-word (`cpblk` / multiple moves) and **tear under concurrent data races**!

#### Why `Span<T>` MUST Be Stack-Confined While `Memory<T>` Survives Tearing Safely
Comparing a hypothetical heap-storable `Span<T>` (`(ref T _reference, int _length)`) against actual heap-storable `Memory<T>` (`(object? _object, int _index, int _length)`, `Memory.cs:26-28`) exposes a sharp memory-safety boundary verified via our exhaustive interleaving probe (`swift_vwt_layout_and_clr_tearing_sim.py`):

- **Hypothetical unconfined `Span<T>` (4 word-level interleavings between `small(len=2)` and `large(len=400)`)**: `1 / 4` torn states produces `(ref=arr_small[len=2], length=400)`—**directly bypassing bounds checks and yielding arbitrary out-of-bounds heap read/write (memory corruption)**! Stack confinement (`IsByRefLike` + `Memory-model.md:64-66` forbidding cross-thread stack-local sharing) eliminates data races on `Span<T>` in safe C#.
- **Actual `Memory<T>.Span` (`src/libraries/System.Private.CoreLib/src/System/Memory.cs:280-349`)**: Because `Memory<T>` is a normal 16-byte `struct` storable in shared heap fields, it **can** tear across its three fields (`_object`, `_index`, `_length`). Look at `Memory.cs:321-346`:
  1. It reads `_object` **once** into a local variable `object? tmpObject = _object;` (line 280).
  2. It derives `lengthOfUnderlyingSpan` directly from `tmpObject` (`string.Length`, `T[].Length`, or `MemoryManager<T>.GetSpan().Length`, lines 283–319).
  3. It reads `_index` and `_length` and **re-validates** `(ulong)desiredStartIndex + (ulong)(uint)desiredLength > (ulong)(uint)lengthOfUnderlyingSpan` (line 334), throwing `ArgumentOutOfRangeException` if torn indices exceed `tmpObject`'s true length.
- **Exhaustive 8-state interleaving probe (`small=(arr_small, actual=2, start=0, len=2)` vs. `large=(arr_large, actual=1000, start=500, len=400)`)**:
  - Out-of-bounds memory corruption: **`0 / 8`** (memory safety preserved—never AVs the process).
  - Detected and rejected with `ArgumentOutOfRangeException`: **`3 / 8`**.
  - **Silent logical corruption (wrong slice within bounds)**: **`3 / 8`** (e.g., `(arr_large, start=0, len=2)`, `(arr_large, start=0, len=400)`, `(arr_large, start=500, len=2)`—valid memory addresses, yet slices never constructed by either writer!).

---

### 4. Swift Separate-Compilation Layout Polymorphism via Value Witness Tables (VWT)

**Basis:** documentation (`swiftlang/swift` `docs/ABI/TypeMetadata.rst`, `docs/LibraryEvolution.rst`) + source (`include/swift/ABI/ValueWitness.def`, `include/swift/ABI/MetadataValues.h`) + execution (Python VWT existential/Optional layout probe).

#### Unmonomorphized Generics and ABI-Stable Type Metadata
Unlike C++/Rust (where generic code must see concrete type layouts at compile time and monomorphize) and unlike CoreCLR (which JIT-specializes every value type at runtime), Swift compiles generic functions and callers of **resilient** dynamic libraries (e.g., Apple OS frameworks under Library Evolution) **once, ahead-of-time, without knowing concrete `sizeof(T)`, `alignof(T)`, `strideof(T)`, field offsets, or retain/release structure**.

Swift achieves this through a uniform runtime **Type Metadata** ABI (`docs/ABI/TypeMetadata.rst:10-81`):
- Every type has a unique canonical `Metadata*` pointer (`m1 == m2` iff identical type).
- **Offset `-1` (one pointer-sized word *before* `Metadata*`)** holds a pointer to the type's **`ValueWitnessTable` (VWT)** (`TypeMetadata.rst:29-35`).
- **Offset `0`** holds the `kind` word (`0` for pure-Swift classes; an Objective-C metaclass `isa` pointer `> 2047` for ObjC-interoperating classes on Darwin; `1` Struct; `2` Enum; `3` Optional; `8` Opaque; `9` Tuple; `10` Function; `12` Protocol/Existential; `TypeMetadata.rst:37-65`).
- For **Structs** (`TypeMetadata.rst:66-81`), offset `1` holds the nominal type descriptor, offset `2+` holds the generic argument vector (if generic), followed immediately by a **dynamic field-offset vector** storing each stored property's byte offset—allowing resilient libraries to add, remove, or reorder stored properties without recompiling clients (`docs/LibraryEvolution.rst:354-373`) unless the struct opts out with **`@frozen`** (lines 439–447).

#### Complete Value Witness Table Layout (`ValueWitness.def` & `MetadataValues.h`)
The VWT (`include/swift/ABI/ValueWitness.def:99-294`) provides the exact operational semantics of opaque values:

| Category | VWT Member | Signature / Encoding | Operational Role |
| :--- | :--- | :--- | :--- |
| **Buffer** | `initializeBufferWithCopyOfBuffer` | `T* (B* dst, B* src, M* self)` | Copy-init a 3-word existential value buffer (inline memcpy or heap box alloc/retain). |
| **Lifecycle** | `destroy` | `void (T* obj, M* self)` | Run ARC releases / `deinit` hooks on an in-place value (no-op if POD). |
| **Copy** | `initializeWithCopy` / `assignWithCopy` | `T* (T* dst, T* src, M* self)` | Copy-construct into uninitialized memory / copy-assign over live `dst` (retaining references). |
| **Move (Take)** | `initializeWithTake` / `assignWithTake` | `T* (T* dst, T* src, M* self)` | Move-construct or move-assign invalidating `src`; avoids ARC traffic if bitwise-takable (`!IsNonBitwiseTakable`). |
| **Single-Payload Enum** | `getEnumTagSinglePayload` / `storeEnumTagSinglePayload` | `uint (const T*, uint emptyCases, M*)` / `void (T*, uint whichCase, uint emptyCases, M*)` | Polymorphically inspect/write `Optional<T>` or single-payload enum discriminants using `extraInhabitantCount` without knowing `T`'s layout! |
| **Layout Data** | `size`, `stride`, `flags`, `extraInhabitantCount` | `size_t`, `size_t`, `uint32_t`, `uint32_t` | `stride >= 1` even for zero-sized `()`; alignment encoded as mask `align - 1` in `flags & 0xFF`. |
| **Multi-Payload Enum** (conditional) | `getEnumTag`, `destructiveProjectEnumData`, `destructiveInjectEnumTag` | Present iff `flags & HasEnumWitnesses` | Dynamic tag inspection and in-place payload extraction/injection for resilient enums. |

Key **`TargetValueWitnessFlags`** bits (`include/swift/ABI/MetadataValues.h:173-189`):
- `AlignmentMask = 0x000000FF` (low bits that must be zero in aligned pointers; `alignof = (flags & 0xFF) + 1`)
- `IsNonPOD = 0x00010000` (requires `destroy`/copy witnesses beyond raw `memcpy`)
- `IsNonInline = 0x00020000` (cannot fit inline in a 3-word `ValueBuffer` or is non-bitwise-takable -> must heap-box inside existential containers)
- `HasSpareBits = 0x00080000` (unused tag bits inside payload representation)
- `IsNonBitwiseTakable = 0x00100000` (moving changes address-sensitive state, e.g., relative pointers or `weak` references registered in side tables)
- `HasEnumWitnesses = 0x00200000`, `Incomplete = 0x00400000`
- `IsNonCopyable = 0x00800000` (SE-0390 `~Copyable` move-only types!), `IsNonBitwiseBorrowable = 0x01000000`, `IsAddressableForDependencies = 0x02000000`.

#### Dynamic Stack Allocation, Existential Containers, and Extra-Inhabitant Compression
When executing an unspecialized generic function `func swap<T>(_ a: inout T, _ b: inout T)`:
1. The caller passes `a` and `b` **indirectly by address** along with `T`'s `Metadata*` (and any `ProtocolWitnessTable*` conformances).
2. The callee reads `vwt = *(Metadata**)((char*)meta - sizeof(void*))`, allocates a temporary stack slot dynamically (`alloca(vwt->size)` aligned to `(vwt->flags & 0xFF) + 1`), and invokes `vwt->initializeWithTake(tmp, a, meta)` -> `vwt->initializeWithTake(a, b, meta)` -> `vwt->initializeWithTake(b, tmp, meta)`—zero heap allocation, zero monomorphization!
3. **Existential Containers (`any Protocol` / `Any`)** store a fixed 3-word inline `ValueBuffer` (`NumWords_ValueBuffer = 3`, `MetadataValues.h:46`, 24 bytes on 64-bit) alongside `Metadata*` and `PWT*` pointers. Verified via our formal layout probe (`swift_vwt_layout_and_clr_tearing_sim.py`):

| Swift Type (64-bit) | `size` | `align` | `extraInhabitantCount` | Existential Storage (`any P`) | `Optional<T>` Size |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `Int64` | 8 B | 8 B | `0` | Inline (3-word buffer) | 9 B (extra tag byte) |
| `Bool` | 1 B | 1 B | `254` (`0x02..0xFF`) | Inline (3-word buffer) | **1 B** (0-byte tag overhead!) |
| Class ref (`HeapObject*`) | 8 B | 8 B | `4096` (null/zero page) | Inline (3-word buffer) | **8 B** (0-byte tag overhead!) |
| `Point3D` (`3x Double`) | 24 B | 8 B | `0` | Inline (3-word buffer) | 25 B |
| `Vec4D` (`4x Double`) | 32 B | 8 B | `0` | **Heap boxed** (`IsNonInline`, `32 > 24`) | 33 B |
| `WeakBox` (`weak var r: C?`) | 8 B | 8 B | `0` | **Heap boxed** (`IsNonBitwiseTakable` -> `IsNonInline`) | 9 B |

*Performance note*: Within a single compilation module (or for `@inlinable` / `@_specialize` stdlib generics), Swift's SIL `GenericSpecializer` opportunistically monomorphizes hot call sites to eliminate VWT indirect calls—treating specialization strictly as an **optimization**, never as an ABI or semantic prerequisite.

---

### 5. Swift CoW ARC Uniqueness and Objective-C `objc_msgSend` Interop Boundaries

**Basis:** source (`swiftlang/swift` `RefCount.h`, `HeapObject.cpp`, `SwiftObject.mm`, `ContiguousArrayBuffer.swift`, `TypeMetadata.rst`).

#### Three-Tier Reference-Count State Machine (`RefCount.h`)
Swift heap objects (`HeapObject`) store an `isa` metadata word followed by an atomic `InlineRefCounts` word encoding **three distinct reference counts** across two storage regimes (`stdlib/public/SwiftShims/swift/shims/RefCount.h:43-130`):

1. **Inline regime (initial state, no weak refs)**: Packs `StrongExtraRefCount` (stored as `strong_count - 1`, so physical `0` = logical `1`), `UnownedRefCount` (initialized to `1` on behalf of the strong count), `IsDeiniting`, `PureSwiftDealloc`, and `UseSlowRC = 0` into one atomic pointer-sized word.
2. **Side-table regime (one-way transition on first `weak` reference or overflow)**: Allocates a `HeapObjectSideTableEntry` pointing back to the object and holding `(StrongExtra, Unowned, Weak, Flags)`; the object's inline word stores the side-table pointer with `UseSlowRC = 1`. Weak references point to the **side table** (not the object directly), allowing the object's memory to be freed as soon as `Unowned == 0` even while stale `weak` references remain (`weak` loads read `IsDeiniting` and return `nil`). Transitioning to a side table is permanent to avoid ABA races.

#### Exact Copy-on-Write Uniqueness Semantics and Pitfalls
Swift value collections (`Array`, `Dictionary`, `Set`, `String`, `Data`) store elements in a reference-counted heap buffer and preserve value semantics via **Copy-on-Write (CoW)**: mutating operations mutate in-place iff the buffer is uniquely referenced, otherwise allocating and copying the backing store.

Inspecting `RefCount.h:622-639, 971-980`, `SwiftObject.mm:1507-1531`, and `ContiguousArrayBuffer.swift:812-851` reveals four critical invariants:

1. **Exact predicate (`InlineRefCountBits::isUniquelyReferenced`, `RefCount.h:637-638`)**:
   ```cpp
   return !getUseSlowRC() && !getIsDeiniting() && getStrongExtraRefCount() == 0;
   ```
   When `bits.hasSideTable()` is true, `RefCounts::isUniquelyReferenced()` (`RefCount.h:975-976`) delegates to `bits.getSideTable()->isUniquelyReferenced()`, checking the side table's `StrongExtraRefCount == 0`.
2. **Weak and unowned references do NOT trigger CoW copies**: `RefCount.h:631` explicitly notes `// Unowned: don't care`, and weak references live in the side table's `weakBits` without incrementing `StrongExtraRefCount`. Conversely, **immortal objects** (e.g., the static empty-array singleton) have max/immortal refcounts and always return `false`.
3. **TSan acquire barrier on uniqueness (`SwiftObject.mm:1510-1516`)**: When `swift_isUniquelyReferenced_nonNull_native` observes `unique == true`, it emits `tsan::acquire(object)` (paired with release semantics on other threads' `swift_release`), synchronizing prior reads on releasing threads before the unique owner mutates the buffer in-place.
4. **SIL CoW optimizer brackets (`ContiguousArrayBuffer.swift:825-851`)**: Stdlib buffer mutation calls `Builtin.beginCOWMutation(&_storage)` before mutating and `endCOWMutation` afterward, allowing ARC optimization passes to treat buffer storage as immutable outside the bracket and hoist loads / elide redundant uniqueness checks.
5. **Silent $O(N)$ copy hazard**: Any stray extra strong reference—such as passing an array into a closure, iterating while mutating a copy, or holding an unconsumed ARC temporary before dead-value shrinking—bumps `StrongExtraRefCount >= 1`, silently degrading an amortized $O(1)$ mutation into an $O(N)$ buffer copy without compile-time warning.

#### Objective-C `objc_msgSend` Interop and the Bridged CoW Penalty
On Darwin platforms (`SWIFT_OBJC_INTEROP = 1`), Swift classes interoperate bidirectionally with Objective-C:
- **Unified `isa` & `objc_msgSend`**: Swift class metadata's offset-0 word is an Objective-C metaclass `isa` pointer (`> 2047`, `TypeMetadata.rst:43-52`), allowing `id`-typed ObjC callers to invoke `@objc` Swift methods via `objc_msgSend` selector lookup and allowing `@objc dynamic` Swift methods to participate in Objective-C runtime swizzling (`method_exchangeImplementations`) and KVO (bypassing static/vtable Swift dispatch). `swift::_swift_getClass` (`SwiftObject.mm:78-87`) also checks `isObjCTaggedPointer(object)` before dereferencing `isa` because small `NSString`/`NSNumber` instances pack payload bits directly into the pointer address.
- **Uniqueness returns `false` for all ObjC objects (`SwiftObject.mm:1524-1531`)**:
  ```cpp
  bool swift::swift_isUniquelyReferencedNonObjC_nonNull(const void* object) {
    assert(object != nullptr);
    return
  #if SWIFT_OBJC_INTEROP
      usesNativeSwiftReferenceCounting_nonNull(object) &&
  #endif
      swift_isUniquelyReferenced_nonNull_native((const HeapObject*)object);
  }
  ```
  Because Objective-C `NSObject` subclasses can sit in autorelease pools, override `retain`/`release`, or use custom non-Swift refcounting, Swift cannot trust ObjC reference counts for thread-safe in-place CoW mutation. Bridging an `NSArray` into a Swift `Array` (zero-copy lazily via `_CocoaArrayWrapper`) therefore **guarantees a defensive native buffer copy** on the first mutation in Swift!

---

### 6. Julia Symmetric Open Multiple Dispatch and the Diagonal Subtyping Rule

**Basis:** source (`JuliaLang/julia` `src/subtype.c`, `base/errorshow.jl`) + derived (Zappa Nardelli et al., OOPSLA 2018, DOI `10.1145/3276483`) + execution (Python Julia subtyping & dispatch formal probe).

#### Type Lattice: Invariance, Tuple Covariance, and `UnionAll`
Julia replaces single-dispatch receiver classes with **open symmetric multiple dispatch** over runtime concrete types:
- **Nominal concrete leaves**: Every concrete `struct` / primitive type is a leaf of the nominal subtype tree (`Int64 <: Signed <: Integer <: Real <: Number <: Any`); only `abstract type`s can be subtyped.
- **Parametric invariance vs. `Tuple` covariance**: Parametric nominal types are strictly **invariant** (`Vector{Int64} <: Vector{Real}` is `false`) so mutable containers avoid Java/CLR's covariant `ArrayStoreException` runtime store checks and enable unboxed flat memory layouts (`Vector{Int64}` stores contiguous 64-bit integers). Conversely, immutable `Tuple` types are **covariant** (`Tuple{Int64} <: Tuple{Real}` is `true`) because function call signatures are encoded as tuple types `Tuple{typeof(f), Arg1, Arg2, ...}`!
- **Existential bounded quantification (`UnionAll`)**: Writing `Vector{<:Real}` desugars to `Vector{T} where T<:Real` ($\exists T \le \text{Real}.\; \text{Vector}\{T\}$), restoring polymorphism over invariant containers.

#### The Diagonal Rule (`src/subtype.c`)
A subtle and formally decisive rule governs method signatures where a `UnionAll` type parameter `T` appears multiple times, such as `f(x::T, y::T) where T<:Real` (signature `Tuple{typeof(f), T, T} where T<:Real`). Under naive existential subtyping without restriction, `Tuple{Int64, Float64}` would match `Tuple{T, T} where T<:Real` by instantiating `T = Real`—completely defeating the programmer's intent that `x` and `y` have the *same* concrete type!

As reconstructed by Zappa Nardelli et al. (OOPSLA 2018, DOI `10.1145/3276483`) and implemented in `JuliaLang/julia` `src/subtype.c:80-145, 407-414`, Julia enforces the **diagonal rule**:
- Each `jl_varbinding_t` tracks `occurs_cov` / `cov_diag` (`cov_count(vb) = max(occurs_cov, cov_diag)`, lines 411–414) and a cached static structural flag `body_occurs_inv` (`var_occurs_invariant(u->body, u->var)`, lines 139–144).
- **Rule**: If a `UnionAll` type variable `T` occurs **covariantly at least twice** (`cov_count(vb) > 1`) and **does NOT occur invariantly** (`!body_occurs_inv`), then `T` is **diagonal** and may only be instantiated with a **concrete** type!

Verified directly in our formal subtyping probe (`julia_subtyping_and_world_age_sim.py`):

| Subtyping Query | Diagonal Variable? | Result | Reason |
| :--- | :--- | :--- | :--- |
| `Vector{Int64} <: Vector{Real}` | N/A | **`false`** | Parametric nominal invariance. |
| `Tuple{Int64} <: Tuple{Real}` | N/A | **`true`** | Covariant `Tuple` elements. |
| `Tuple{Int64, Int64} <: Tuple{T, T} where T<:Real` | Yes (`T`) | **`true`** | `T = Int64` is concrete and `Int64 <: Real`. |
| `Tuple{Int64, Float64} <: Tuple{T, T} where T<:Real` | Yes (`T`) | **`false`** | No single concrete `T` is a supertype of both `Int64` and `Float64`. |
| `Tuple{Real, Real} <: Tuple{T, T} where T<:Real` | Yes (`T`) | **`false`** | `Real` is **abstract**, disallowed for diagonal variable `T`! |
| `Tuple{Vector{Real}, Real} <: Tuple{Vector{T}, T} where T<:Real` | **No** (`T` invariant in `Vector{T}`) | **`true`** | `body_occurs_inv == true` exempts `T` from the diagonal rule, permitting `T = Real`! |

#### Specificity Ordering, Call-Time Ambiguities, and Type Piracy
Method lookup compares applicable method signatures symmetrically across all tuple positions using `jl_type_morespecific` (`src/subtype.c:7780-7796`), which checks strict subtyping first (`!jl_subtype(b, a) && jl_subtype(a, b)`) and falls back to structural specificity (`type_morespecific_`) for incomparable signatures (such as `Tuple{Int, Any}` vs. `Tuple{T, T} where T`).

Because dispatch is **open** (any module can add methods to any existing generic function) and **symmetric** (no privileged receiver argument), adding `amb(::Int64, ::Real)` and `amb(::Real, ::Int64)` succeeds silently at definition time. Calling `amb(1, 2)` (`Tuple{Int64, Int64}`) detects multiple maximal candidates and raises **`MethodError: amb(::Int64, ::Int64) is ambiguous`** at runtime (`base/errorshow.jl:282-285, 433-443`). Defining methods whose function and all argument types are owned by *other* packages—**type piracy**—can silently hijack dispatch or inject runtime `MethodError` ambiguities into unrelated libraries.

---

### 7. Julia Monotonic World-Age JIT Epoch Isolation and Invalidation Cascades

**Basis:** source (`JuliaLang/julia` `src/julia.h`, `src/gf.c`, `src/builtins.c`, `base/reflection.jl`, `base/errorshow.jl`) + derived (Belyakova et al., OOPSLA 2020, DOI `10.1145/3428275`) + execution (Python world-age epoch & invalidation simulator).

#### The Dynamic `eval` vs. Speculative Inlining Dilemma
In an interactive language combining open multiple dispatch with runtime `eval`, defining a new method `f(::Int64) = 2` while a compiled caller `g(x)` has already inlined `f(::Number) = 1` threatens either soundness (if new code executes stale methods) or performance/complexity (requiring JVM-style safepoint deoptimization and on-stack replacement across every live frame).

Julia resolves this cleanly using **monotonic world-age epochs** (formalized in the *Juliette* calculus by Belyakova, Chung, Gelinas, Nash, Tate, and Vitek, OOPSLA 2020, DOI `10.1145/3428275`):

1. **Global Monotonic World Counter (`src/gf.c:51-57, 4150-4163`)**:
   ```c
   // JuliaLang/julia src/gf.c:4150-4162
   JL_DLLEXPORT void jl_method_table_insert(jl_methtable_t *mt, jl_method_t *method, jl_tupletype_t *simpletype) {
       jl_typemap_entry_t *newentry = jl_method_table_add(mt, method, simpletype);
       JL_LOCK(&world_counter_lock);
       if (!jl_atomic_load_relaxed(&allow_new_worlds))
           jl_error("Method changes have been disabled via a call to disable_new_worlds.");
       size_t world = jl_atomic_load_relaxed(&jl_world_counter) + 1;
       jl_atomic_store_relaxed(&method->primary_world, world);
       jl_method_table_activate(newentry);
       jl_atomic_store_release(&jl_world_counter, world);
       JL_UNLOCK(&world_counter_lock);
   }
   ```
2. **Versioned Methods and `CodeInstance` Validity Intervals (`src/julia.h:524-582`)**:
   - Every `jl_method_t` is active over `[primary_world, deleted_world)`.
   - Every compiled specialization `jl_code_instance_t` carries atomic `_Atomic(size_t) min_world` and `_Atomic(size_t) max_world` (`julia.h:571-572`, initially `max_world = ~(size_t)0`, i.e., $\infty$) along with inferred `rettype`, `exctype`, and `rettype_const`.
3. **Task-Local Epoch Freezing (`jl_task_t.world_age`, `src/julia.h:2642`)**:
   - Every running task holds a fixed `ct->world_age` established when entering top-level evaluation (REPL/script) or spawned from its parent task.
   - All normal calls inside that task resolve methods strictly against `primary_world <= ct->world_age < deleted_world`. Therefore, **within a running epoch, the visible method table is immutable**: LLVM-compiled code can devirtualize, inline, and constant-fold aggressively with **zero OSR / zero mid-frame deoptimization**!
   - Special case: Inside pure `@generated` function generators (`ct->ptls->in_pure_callback`, `gf.c:54-55`), `jl_get_world_counter()` returns `~(size_t)0` (preventing world-age leaks into pure AST generation).
4. **Explicit Epoch Crossing (`Base.invokelatest` / `invoke_in_world`)**:
   - If a function running in world `W` invokes `eval(:(only_new(x::Int64) = 99))` (advancing `jl_world_counter` to `W + 1`) and immediately calls `only_new(1)`, dispatch executes in frozen world `W` and throws (`base/errorshow.jl:385-387`):
     > `MethodError: ... The applicable method may be too new: running in world age W, while current world is W+1.`
   - Calling **`Core.invokelatest(f, args...)`** (`jl_f_invokelatest`, `src/builtins.c:1055-1063`) explicitly crosses the epoch boundary:
     ```c
     size_t last_age = ct->world_age;
     if (!ct->ptls->in_pure_callback)
         ct->world_age = jl_atomic_load_acquire(&jl_world_counter);
     jl_value_t *ret = jl_apply(args, nargs);
     ct->world_age = last_age;
     return ret;
     ```
     Similarly, `jl_f_invoke_in_world(world, f, args...)` (`builtins.c:1067-1077`) executes in `min(world, jl_world_counter)`, and the `@invokelatest` macro (`base/reflection.jl:1367-1396`) resolves literal global bindings (`getglobalref(gr, world)`) consistently in the target world before calling `invoke_in_world`. Because `invokelatest` crosses epochs, the compiler treats it as an opaque dynamic call barrier (blocking cross-epoch inlining).
5. **Backedge Invalidation Cascades (`src/gf.c:3140-3223, 3786-3792, 3924-3939`)**:
   - Whenever type inference specializes caller `M_caller` relying on a dispatch result to callee `M_callee`, Julia records `M_caller` in `M_callee`'s `jl_method_instance_t.backedges` (`julia.h:524-536`).
   - When `jl_method_table_activate_with_record` inserts a new method overriding or shadowing a previously inferred dispatch, it walks transitive `backedges` (`_invalidate_dispatch_backedges`) and **clamps every affected `CodeInstance.max_world` from `INF` to `new_world - 1`** (and invalidates `mt->cache` entries).
   - **Verified in our world-age simulator (`julia_subtyping_and_world_age_sim.py`)**: After compiling `caller` in `task_world = 4` (binding `f(::Number) = 1` with `CI valid = [2, INF]`), inserting `f(::Int64) = 2` bumps `world_counter = 5` and clamps `CI` to `[2, 4]`. Calls inside `task_world = 4` still soundly execute the compiled `CI` (`f(::Number) = 1`); calls via `invokelatest` (world `5`) see `CI` as expired (`5 > 4`), re-dispatch to `f(::Int64) = 2`, and trigger recompilation for future epochs. When a package adds a broad method on a ubiquitous Base function (e.g., `Base.convert`, `Base.show`, `Base.iterate`), thousands of transitive `backedges` can be clamped in a single `using`, causing substantial recompilation latency ("TTFX / invalidations").

---

### 8. Cross-Runtime Architectural Trade-Off Matrix

**Basis:** derived (synthesizing Findings 1–7).

| Dimension | .NET CLR (`dotnet/runtime`) | Swift (`swiftlang/swift`) | Julia (`JuliaLang/julia`) |
| :--- | :--- | :--- | :--- |
| **Generic Polymorphism Model** | Hybrid reified: `__Canon` shared JIT code + `Dictionary` for refs; full JIT specialization for value types. | Unmonomorphized AOT layout polymorphism via `Metadata*` + **Value Witness Table** (offset `-1`) + `PWT*`; optional SIL specialization. | Full JIT type-specialization per concrete argument tuple (`MethodInstance` / `CodeInstance`) + union splitting. |
| **Separate Compilation / ABI Stability** | Strong assembly-level binary compat via IL metadata & JIT compilation at load/run time. | **Strongest AOT native ABI stability** (Library Evolution: resilient structs/enums via VWT + dynamic field offsets; `@frozen` opt-out). | Weak AOT ABI stability (package precompilation caches tied to exact method-table worlds & invalidation edges). |
| **Dynamic Dispatch & Evolution** | Single-dispatch vtables + interface dispatch + GVM dictionary stubs; dynamic assembly load. | Static / vtable / PWT dispatch + Darwin `objc_msgSend` (`@objc dynamic` swizzling). | **Symmetric open multiple dispatch** (`jl_type_morespecific`, diagonal rule, call-time ambiguity `MethodError`). |
| **Dynamic Code / Invalidation Strategy** | Dynamic IL / Collectible `AssemblyLoadContext`; Tiered Compilation & OSR. | Static AOT binaries (no general runtime `eval`); ObjC runtime swizzling via dynamic dispatch. | **Monotonic world-age epochs** (`jl_world_counter`, `[min_world, max_world]`, `backedges` clamping, `invokelatest` barrier, zero OSR). |
| **Interior Pointer & Buffer Safety** | `Span<T>` (`ref struct`, `IsByRefLike`) stack-confined GC interior `byref`; `gpAllowByRefLike` for generic use; `Memory<T>` heap-storable with defensive bounds re-check. | `UnsafeBufferPointer` (unsafe), `Span` / non-escapable lifetime types (`~Escapable`), CoW native buffers via `beginCOWMutation`. | GC-managed unboxed `Array` / `Memory{T}` + `GC.@preserve` scoping for `Ptr{T}` C pointers. |
| **Value Invariant & Concurrency Hazards** | Implicit all-zero `default(T)` breaks non-zero invariants (`ImmutableArray<T>`); >pointer-width heap structs tear under race. | No implicit zero-init; strict definite initialization; CoW silent $O(N)$ copy on extra strong ref or ObjC-bridged object. | Immutable `struct`s avoid mutation races; type piracy & broad method extensions trigger massive backedge invalidation cascades. |
| **FFI Boundary Cost / Semantics** | P/Invoke marshaling + `GCHandle` pinning (or `Span<T>` over unmanaged non-reference `T`). | Zero-overhead C/C++ interop + bidirectional ObjC `isa`/`objc_msgSend` (but ObjC objects fail CoW uniqueness checks). | Direct zero-wrapper `ccall` to C ABI symbols (requires `GC.@preserve` to prevent GC relocation/collection across pointer use). |

## Boundaries

- **Not examined**:
  - **Direct native binary execution of `.NET`, `swiftc`, and `julia` toolchains**: None of `dotnet`, `swift`, or `julia` were installed on the Linux observation host. All claims about these three runtimes are grounded in direct primary-source inspection at the pinned commits, normative standards/peer-reviewed papers, and standalone Python formal models replicating the exact upstream algorithms—not live compilation/execution of C#, Swift, or Julia binaries.
  - **Mono and NativeAOT runtimes**: Only CoreCLR (`src/coreclr/vm/`) and `System.Private.CoreLib` in `dotnet/runtime` were inspected; NativeAOT's ahead-of-time generic sharing (`UniversalShared` / `ReadyToRun` constraints) and Mono's AOT/interpreter pipelines were not examined.
  - **Swift Embedded Mode, `~Escapable` lifetime dependencies, and Swift 6 strict concurrency actor isolation**: Beyond noting `IsNonCopyable`, `IsNonBitwiseBorrowable`, and `IsAddressableForDependencies` in `MetadataValues.h:183-185`, full Swift 6 region-based isolation and `~Escapable` `Span` lowering were not examined.
  - **Julia `OverlayMethodTable` / `Core.Compiler` abstract interpretation lattice**: Only `src/subtype.c`, `src/gf.c`, `src/builtins.c`, `src/julia.h`, `base/reflection.jl`, and `base/errorshow.jl` were directly inspected; Julia's overlay method tables (`@overlay`) and full `Core.Compiler` type-inference fixed-point loop were not examined.
- **Unknown**:
  - **CoreCLR JIT compliance with `Memory-model.md` data-dependent read and object-assignment guarantees**: `dotnet/runtime/docs/design/specs/Memory-model.md:146` explicitly records uncertainty (`"It is believed that compiler optimizations do not violate the ordering guarantees... but further investigations are needed"`, citing `https://github.com/dotnet/runtime/issues/79764`); whether RyuJIT preserves these guarantees across all ARM64/x64 optimizations remains unverified.
- **Known not to apply**:
  - **Objective-C `isa` / `objc_msgSend` CoW penalty on Linux/Windows Swift**: Known **not** to apply when `SWIFT_OBJC_INTEROP == 0` (`SwiftObject.mm:79, 1527`), where Swift classes use pure-Swift metadata (`kind == 0`) and never bridge to `NSObject`.
  - **Out-of-bounds memory corruption via `Memory<T>` tearing**: Known **not** to apply to `System.Memory<T>.Span` in `dotnet/runtime` `fcb04a83f3013e65d573dc0ec240c7a5a720db3a` (`Memory.cs:280-349`); tearing `Memory<T>` causes logical wrong-slice corruption or `ArgumentOutOfRangeException`, not out-of-bounds access violations.
  - **Weak/unowned references forcing Swift CoW copies**: Known **not** to apply; `RefCount.h:631-638, 973-980` proves uniqueness depends solely on `StrongExtraRefCount == 0` (inline or in side table).
- **Unsupported**:
  - **Storing `Span<T>` or any `IsByRefLike` `ref struct` in a static field, heap class field, boxed `object`, or array**: Explicitly unsupported and rejected at class-load time by CoreCLR (`methodtablebuilder.cpp:4358-4391`).
  - **Creating `Span<T>(void*, int)` when `T` is or contains GC references**: Explicitly unsupported (`Span.cs:111-112`, throws `ArgumentException`).
  - **Calling newly `eval`-ed Julia methods in the same task epoch without `invokelatest`/`invoke_in_world` (or defining methods after `disable_new_worlds`)**: Explicitly unsupported (`errorshow.jl:385-387`; `gf.c:4155-4156`).
- **Attractive stronger conclusions NOT established**:
  - CoreCLR's `Memory<T>.Span` safety under tearing does **not** generalize to arbitrary user-defined multi-word structs containing bounds/indices or unsafe pointers; any custom struct storing `(T[] arr, int start, int len)` that reads fields without snapshotting and re-checking against `arr.Length` remains vulnerable to torn-index logic bugs or `Unsafe.Add` OOB corruption.
  - Julia's world-age epoch isolation does **not** isolate global mutable heap state (`Ref`, `Dict`, mutable structs, `global` non-const bindings) across epochs—only method tables and constant bindings are versioned by `jl_world_counter`.

## Evidence

### Upstream Git Source Inspections (Observed 2026-11-19)

| Repository & Commit | File Path | Symbols / Line Ranges | Role |
| :--- | :--- | :--- | :--- |
| `dotnet/runtime` `fcb04a83f3013e65d573dc0ec240c7a5a720db3a` | `src/coreclr/vm/generics.cpp` | `ClassLoader::CanonicalizeGenericArg`, `IsSharableInstantiation`, `LoadCanonicalGenericInstantiation` (L27–140) | source |
| `dotnet/runtime` `fcb04a83f3013e65d573dc0ec240c7a5a720db3a` | `src/coreclr/vm/genericdict.h` | `enum DictionaryEntryKind`, `DictionaryLayout`, `NUM_DICTIONARY_SLOTS` (L18–178) | source |
| `dotnet/runtime` `fcb04a83f3013e65d573dc0ec240c7a5a720db3a` | `src/coreclr/vm/methodtablebuilder.cpp`, `src/coreclr/inc/corhdr.h` | `WellKnownAttribute::IsByRefLike`, `SetIsByRefLike`, `IDS_CLASSLOAD_BYREF_OR_BYREFLIKE_STATICFIELD` (L1400–1408, 1801–1804, 4358–4391); `gpAllowByRefLike = 0x0020` (`corhdr.h` L847–853) | source |
| `dotnet/runtime` `fcb04a83f3013e65d573dc0ec240c7a5a720db3a` | `src/libraries/System.Private.CoreLib/src/System/Span.cs` | `public readonly ref struct Span<T>`, `_reference`, `_length`, covariance & `IsReferenceOrContainsReferences` guards (L28–127) | source |
| `dotnet/runtime` `fcb04a83f3013e65d573dc0ec240c7a5a720db3a` | `src/libraries/System.Private.CoreLib/src/System/Memory.cs` | `Memory<T>` fields (`_object`, `_index`, `_length`, L21–29); `Memory<T>.Span` tearing defense & bounds re-validation (L263–351) | source |
| `dotnet/runtime` `fcb04a83f3013e65d573dc0ec240c7a5a720db3a` | `src/libraries/System.Collections.Immutable/src/System/Collections/Immutable/ImmutableArray_1.cs` | `ThrowNullRefIfNotInitialized()` default zero-init guards (L167–170, 252–255, 314–317, 346–349) | source |
| `dotnet/runtime` `fcb04a83f3013e65d573dc0ec240c7a5a720db3a` | `docs/design/specs/Memory-model.md` | Alignment, pointer-width atomicity, prohibited speculative writes/reads, data-dependent reads, release-on-object-assignment (L1–300) | normative + documentation |
| `swiftlang/swift` `e96891912c1fbf1174f4faf3f63a9d4deb04e39f` | `include/swift/ABI/ValueWitness.def`, `include/swift/ABI/MetadataValues.h` | All 15 VWT functions/data/enum witnesses (L99–294); `NumWords_ValueBuffer = 3` (L46); `TargetValueWitnessFlags` bitmask (L173–189) | source |
| `swiftlang/swift` `e96891912c1fbf1174f4faf3f63a9d4deb04e39f` | `docs/ABI/TypeMetadata.rst`, `docs/LibraryEvolution.rst` | Offset `-1` VWT, `kind` vs. ObjC `isa > 2047`, Struct field-offset vector (L10–140); resilient struct evolution & `@frozen` (L354–447) | documentation |
| `swiftlang/swift` `e96891912c1fbf1174f4faf3f63a9d4deb04e39f` | `stdlib/public/SwiftShims/swift/shims/RefCount.h`, `stdlib/public/runtime/SwiftObject.mm`, `stdlib/public/core/ContiguousArrayBuffer.swift` | Inline vs. side-table ARC layout & `isUniquelyReferenced()` (L43–130, 622–639, 971–980); `swift_isUniquelyReferenced_nonNull_native` + TSan acquire + `swift_isUniquelyReferencedNonObjC_nonNull` + `_swift_getClass` tagged-pointer check (`SwiftObject.mm` L78–87, 1507–1539); `beginCOWMutation`/`endCOWMutation` (`ContiguousArrayBuffer.swift` L812–851) | source |
| `JuliaLang/julia` `6478933d4232a63baa7286faf5182a8521f6fb05` | `src/julia.h` | `jl_method_instance_t.backedges` (L524–536); `jl_code_instance_t.{min_world,max_world}` (L567–582); `jl_task_t.world_age` (L2642) | source |
| `JuliaLang/julia` `6478933d4232a63baa7286faf5182a8521f6fb05` | `src/gf.c`, `src/builtins.c`, `base/reflection.jl`, `base/errorshow.jl` | `jl_get_world_counter` (L51–57); `invalidate_mt_cache_deferred` & `_invalidate_dispatch_backedges` (L3140–3223, 3786–3792); `jl_method_table_activate_with_record` (L3924–3939); `jl_method_table_insert` (L4150–4163); `jl_f_invokelatest` & `jl_f_invoke_in_world` (`builtins.c` L1055–1077); `@invokelatest` (`reflection.jl` L1367–1396); `"too new"` & ambiguity formatting (`errorshow.jl` L282–285, 385–387, 433–443) | source |
| `JuliaLang/julia` `6478933d4232a63baa7286faf5182a8521f6fb05` | `src/subtype.c` | `jl_varbinding_t`, `cov_diag`, `body_occurs_inv`, `cov_count` diagonal rule (L80–145, 407–414); `jl_type_morespecific` (L7780–7796) | source |

### Peer-Reviewed Literature and Standards

- **ECMA-335 (6th Edition, June 2012)**: *Common Language Infrastructure (CLI)* — Partitions I–III (CTS, `byref`, generics metadata, memory model baseline).
- **Kennedy & Syme (PLDI 2001)**: *Design and Implementation of Generics for the .NET Common Language Runtime*, DOI `10.1145/381694.378797`.
- **Zappa Nardelli, Belyakova, Pelenitsyn, Chung, Bezanson, Vitek (OOPSLA 2018)**: *Julia Subtyping: A Rational Reconstruction*, DOI `10.1145/3276483`.
- **Belyakova, Chung, Gelinas, Nash, Tate, Vitek (OOPSLA 2020)**: *World Age in Julia: Optimizing Method Dispatch in the Presence of Eval*, DOI `10.1145/3428275`.

### Executable Formal Model Probes (Python 3, Observed 2026-11-19)

1. **Julia Subtyping, Diagonal Rule & World-Age Epoch Simulator (`julia_subtyping_and_world_age_sim.py`)**:
   - Observed output:
     ```text
     Vector{Int64} <: Vector{Real}                                            => False
     Tuple{Int64} <: Tuple{Real}                                              => True
     Tuple{Int64,Int64} <: Tuple{T,T} where T<:Real                           => True
     Tuple{Int64,Float64} <: Tuple{T,T} where T<:Real                         => False
     Tuple{Real,Real} <: Tuple{T,T} where T<:Real [DIAGONAL]                  => False
     Tuple{Vector{Real},Real} <: Tuple{Vector{T},T} where T<:Real [INVARIANT] => True
     Initial task_world=4, compiled CI: bound=f(::Number)=1, valid=[2, INF]
     After eval `f(::Int64)=2`: world_counter=5, invalidated_CIs=1, CI valid=[2, 4]
     Same-epoch call at task_world=4: f(::Number)=1 (CI still valid? True)
     invokelatest at world=5:   f(::Int64)=2 (CI valid at new world? False)
     Too-new call at task_world=4: MethodError: no method only_new('Int64',) visible at world_age=4 (current=6)
     invokelatest(only_new, 1):         only_new(::Int64)=99
     Symmetric ambiguity check:         MethodError: amb('Int64', 'Int64') is ambiguous among [('Int64', 'Real'), ('Real', 'Int64')]
     ```
2. **Swift VWT Layout & CLR Struct-Tearing Interleaving Probe (`swift_vwt_layout_and_clr_tearing_sim.py`)**:
   - Observed output:
     ```text
     Int64                      size= 8B align=8B XI=   0 => INLINE (3-word buffer)    Optional<T>.size=9B
     Bool                       size= 1B align=1B XI= 254 => INLINE (3-word buffer)    Optional<T>.size=1B
     ClassRef (HeapObject*)     size= 8B align=8B XI=4096 => INLINE (3-word buffer)    Optional<T>.size=8B
     Point3D (3xDouble)         size=24B align=8B XI=   0 => INLINE (3-word buffer)    Optional<T>.size=25B
     Vec4D (4xDouble)           size=32B align=8B XI=   0 => HEAP BOXED (IsNonInline)  Optional<T>.size=33B
     WeakBox (weak var r: C?)   size= 8B align=8B XI=   0 => HEAP BOXED (IsNonInline)  Optional<T>.size=9B
     Hypothetical unconfined Span<T>: 1/4 states cause OOB memory corruption (why Span<T> MUST be ref struct!)
     Actual Memory<T>.Span (8 torn combinations): OOB=0, caught_ArgumentOutOfRange=3, logical_wrong_slice_in_bounds=3
     ```

## Revalidation

To cheaply verify whether these findings still hold on future releases of `.NET`, Swift, or Julia:

1. **.NET CLR generics, `Span<T>`, and tearing**:
   - Diff `src/coreclr/vm/generics.cpp` (`CanonicalizeGenericArg`), `src/coreclr/inc/corhdr.h` (`CorGenericParamAttr`), `src/libraries/System.Private.CoreLib/src/System/Memory.cs` (`Memory<T>.Span`), and `docs/design/specs/Memory-model.md` (specifically checking whether `https://github.com/dotnet/runtime/issues/79764` on data-dependent reads/object-assignment compiler compliance has been resolved).
   - Where a `dotnet` SDK is available, compile a small C# probe checking `typeof(List<int>) != typeof(List<double>)`, `default(ImmutableArray<int>).IsDefault == true`, and racing two threads mutating a shared `Memory<byte>` field while reading `.Span` to observe `ArgumentOutOfRangeException` or mismatched slices without process crashes.
2. **Swift VWT, CoW ARC, and ObjC interop**:
   - Diff `include/swift/ABI/ValueWitness.def`, `include/swift/ABI/MetadataValues.h` (`NumWords_ValueBuffer`, `TargetValueWitnessFlags`), `stdlib/public/SwiftShims/swift/shims/RefCount.h` (`isUniquelyReferenced`), and `stdlib/public/runtime/SwiftObject.mm` (`swift_isUniquelyReferencedNonObjC_nonNull`).
   - Where `swiftc` is available, compile a generic function with `-enable-library-evolution -emit-sil` to verify VWT witness calls (`copy_addr`/`destroy_addr`) and run `MemoryLayout<Bool?>.size == 1`, `MemoryLayout<AnyObject?>.size == 8`, and `isKnownUniquelyReferenced(&ref)` with a live `weak var` (asserting `true`) vs. an `NSObject` subclass (asserting `false` on Darwin).
3. **Julia subtyping and world age**:
   - Diff `src/subtype.c` (`cov_count`, `body_occurs_inv`, `jl_type_morespecific`), `src/gf.c` (`jl_method_table_insert`, `jl_method_table_activate_with_record`), and `src/builtins.c` (`jl_f_invokelatest`, `jl_f_invoke_in_world`).
   - Where `julia` is available, run a one-liner verifying:
     `julia -e '@assert !(Vector{Int} <: Vector{Real}); @assert !(Tuple{Real,Real} <: Tuple{T,T} where T<:Real); @assert Tuple{Vector{Real},Real} <: Tuple{Vector{T},T} where T<:Real; g() = (@eval h() = 1; try h() catch e; e isa MethodError end && Base.invokelatest(h) == 1); @assert g()'`
