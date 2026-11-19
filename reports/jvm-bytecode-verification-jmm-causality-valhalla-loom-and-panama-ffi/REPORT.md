# JVM Bytecode Verification, JMM Causality, Valhalla Value Layouts, Loom Pinning, and Panama FFM Temporal Safety

## Summary

The Java Virtual Machine (JVM) enforces memory and type safety through a layered contract spanning classfile verification, compiler-synthesized casts, runtime checks, speculative JIT dependency tracking, weak memory ordering, flattened value-object layouts, continuation-based virtual threads, and thread-local-handshake FFI lifetime reclamation. Seven load-bearing invariants and failure modes govern verification, compiler engineering, and FFI integration against HotSpot (`openjdk/jdk` `186489b55b5df61e270174a76104a2af27cc7197` and `openjdk/valhalla` `12e87d09246d366cc74cb409e4c914351256e98b`):

1. **`StackMapTable` verification defers interface soundness to runtime**: For classfile major version `>= 51`, HotSpot strictly mandates single-pass split verification (`ClassVerifier`) with no fallback to legacy type inference and rejects `jsr`/`ret` bytecodes. Critically, `VerificationType::resolve_and_check_assignability` treats every non-array interface target as `java.lang.Object` during static assignability checks; a verified classfile can pass an arbitrary `Object` into a `Runnable`-typed slot without `checkcast`, deferring interface enforcement to runtime `invokeinterface` (`IncompatibleClassChangeError`).
2. **Type erasure relies on synthetic bridge `checkcast`s and covariant array `aastore` checks**: `javac` erases generic parameters and emits `ACC_BRIDGE | ACC_SYNTHETIC` methods (`TransTypes.addBridge`) that cast erased arguments before delegating to specialized overrides; raw-type heap pollution fails lazily with `ClassCastException` at the bridge or call-site cast. Separately, Java array covariance (`String[] <: Object[]`) is unchecked statically at element writes and guarded dynamically by runtime `aastore` / `RefArrayKlass::copy_array` checks throwing `ArrayStoreException`.
3. **Runtime class redefinition invalidates closed-world CHA devirtualization via `evol_method` dependencies**: HotSpot JIT compilers speculatively devirtualize and inline call sites using `Dependencies::DepType` records (`leaf_type`, `unique_concrete_method`, `unique_implementor`, `evol_method`). `java.lang.instrument.Instrumentation.redefineClasses` (JVMTI `VM_RedefineClasses`) forbids hierarchy, field-schema, and method-signature changes, yet replaces method bodies at a safepoint and invokes `flush_dependent_code()`, marking all dependent compiled `nmethod`s (including callers that inlined the redefined method) `not entrant` for deoptimization.
4. **Manson–Pugh–Adve JMM causality forbids OOTA cycles but invalidates standard compiler optimizations**: JLS §17.4.8 defines causality via iterative justifying execution chains ($C_0 \subseteq C_1 \subseteq \dots \subseteq C_k$), blocking out-of-thin-air (`OOTA`) values in TC4/TC5 while permitting speculative cross-thread writes in TC1. However, Ševčík and Aspinall (ECOOP 2008) proved that redundant read elimination, irrelevant read introduction, and roach-motel code motion are unsound under JMM causality, and deciding causality for arbitrary finite executions is undecidable. Modern JDK concurrency relies in practice on `VarHandle` access modes (`Plain`, `Opaque`, `Acquire`/`Release`, `Volatile`; JEP 193) alongside DRF-SC.
5. **Project Valhalla preserves tearing-free atomicity by default and isolates tearing to explicit `@LooselyConsistentValue` layouts**: In `openjdk/valhalla` (`lworld`), HotSpot distinguishes six `LayoutKind` encodings (`REFERENCE`, `BUFFERED`, `NULL_FREE_NON_ATOMIC_FLAT`, `NULL_FREE_ATOMIC_FLAT`, `NULLABLE_ATOMIC_FLAT`, `NULLABLE_NON_ATOMIC_FLAT`). JEP 401 value objects remain tearing-free by default (using atomic flat layouts with an embedded 1-byte null marker and an all-zero reset instance, or falling back to `REFERENCE` when exceeding hardware atomic width). Only null-restricted fields of `@LooselyConsistentValue` types select `NULL_FREE_NON_ATOMIC_FLAT`, allowing racy multi-word updates to tear and expose field combinations never produced by any constructor; HotSpot explicitly disables atomic flattening inside loosely consistent containers (`can_use_atomic_flat == false`) to prevent outer tearing from tearing inner atomic value fields.
6. **Project Loom eliminated `synchronized` pinning in JDK 24+ (JEP 491), leaving native frames and VM critical sections as pinning boundaries**: In JDK 21–23 (JEP 444), blocking or contending inside `synchronized` pinned virtual threads to OS carrier threads. In `openjdk/jdk` HEAD and OpenJDK 27.0.1, `Continuation.Pinned` no longer has a `MONITOR` variant—only `NATIVE`, `CRITICAL_SECTION`, and `EXCEPTION` remain—and `ObjectMonitor` unmounts contending virtual threads via heap-frozen frames and a dedicated unblocker queue. Native JNI/FFM frames and VM `<clinit>` class initializers still pin the carrier thread.
7. **Project Panama FFM achieves zero-lock hot-path reads and deterministic cross-thread `close()` via HotSpot handshakes**: `Arena.ofConfined()` checks thread ownership and `state >= OPEN` in plain mode (`MemorySessionImpl.checkValidStateRaw`), throwing `WrongThreadException` or `IllegalStateException`. `Arena.ofShared()` keeps the identical plain-mode hot path and guarantees deterministic use-after-free safety during `close()` by executing `ScopedMemoryAccess_closeScope`, which runs a global HotSpot `Handshake::execute` (`CloseScopedMemoryHandshakeClosure`) to synchronize visibility, inject async `ScopedAsyncExceptionHandshakeClosure` unwinding into `@Scoped` frames (spinning until delivered before `free`/`munmap`), and deoptimize compiled frames (`Deoptimization::deoptimize`) whose strip-mined loops may have hoisted liveness checks past a safepoint.

## Applicability

These findings govern the following durable upstream subjects and their specific interactions:

- **Mainline HotSpot VM and JDK libraries (`openjdk/jdk` commit `186489b55b5df61e270174a76104a2af27cc7197`, branch `master`)**: Direct source inspection covers `ClassVerifier`, `VerificationType`, `TransTypes`, `ObjArrayKlass`/`RefArrayKlass`, `Dependencies`, `VM_RedefineClasses`, `VarHandle`, `Continuation`, `VirtualThread`, `ObjectMonitor`, `MemorySessionImpl`/`ConfinedSession`/`SharedSession`, and `ScopedMemoryAccess_closeScope`. Note that this mainline revision already incorporates JEP 491 (unpinned `synchronized` monitors), JEP 454 (finalized Panama FFM API), and preparatory Valhalla infrastructure (`JVM_ACC_IDENTITY` in `objArrayKlass.cpp`, `mismatch_calling_convention` in `dependencies.hpp`, and early-larval strict-field verification in `verifier.cpp`).
- **Project Valhalla (`openjdk/valhalla` commit `12e87d09246d366cc74cb409e4c914351256e98b`, branch `lworld`)**: Direct source inspection covers `LayoutKind`, `fieldLayoutBuilder.cpp`, `@LooselyConsistentValue`, and `@NullRestricted`. Because Valhalla value-class flattening and null-restricted types are still evolving toward JEP 401/preview finalization, layout heuristics (`UseFieldFlattening`, `UseNullableAtomicValueFlattening`, size budgets) are specific to the pinned `lworld` revision and must not be assumed stable across earlier LW4/primitive-class prototypes or unshipped future JEPs.
- **Live execution environment (OpenJDK 27.0.1, Linux x86_64, 64-Bit Server VM)**: Directly verifies bytecode verification (`-Xverify:all`), synthetic bridge generation (`javap -v`), `ArrayStoreException`, `java.lang.instrument` CHA/`evol_method` deoptimization (`-XX:+PrintCompilation -Xlog:redefine+class+nmethod=debug`), JEP 491 `synchronized` unpinning vs. `<clinit>` pinning via JFR (`jdk.VirtualThreadPinned`), and Panama FFM `Arena.ofConfined()` / `Arena.ofShared()` temporal safety.
- **Version-split qualifications**:
  - **Bytecode verification**: Classfiles with major version `< 50` (pre-JDK 6) use legacy type-inference verification; version `50` (JDK 6) attempts split verification and falls back to type inference on `VerifyError`/`ClassFormatError`; version `>= 51` (JDK 7+) enforces strict split verification with zero fallback and bans `jsr`/`ret`.
  - **Virtual-thread `synchronized` pinning**: Applies to **JDK 21–23** (JEP 444); **known not to apply** to **JDK 24+** (JEP 491, verified on OpenJDK 27.0.1 and `openjdk/jdk` HEAD), except when a native frame or VM critical section also occupies the virtual thread stack.
  - **JMM causality & transformations**: Applies normatively to JLS §17.4 (Java 5 onward) as formalized in Manson–Pugh–Adve (POPL 2005) and analyzed by Ševčík–Aspinall (ECOOP 2008), Batty et al. (ESOP 2015), and Kang et al. (POPL 2017). `VarHandle` modes apply from JDK 9 onward (JEP 193).

## Findings

### 1. `StackMapTable` Split Bytecode Verification and Deferred Interface Soundness

**Basis:** normative (JVMS §4.10.1) + source (`openjdk/jdk` `verifier.hpp`, `verifier.cpp`, `verificationType.cpp`, `stackMapFrame.cpp`) + execution (OpenJDK 27.0.1 `-Xverify:all`).

#### Split Verification Dispatch and Version Thresholds
HotSpot selects between the linear-time split verifier (`ClassVerifier`, JVMS §4.10.1 verification by type checking) and the legacy fixed-point dataflow verifier (`inference_verify`, JVMS §4.10.2 verification by type inference) using classfile major version constants (`src/hotspot/share/classfile/verifier.hpp:62`, `verifier.cpp:68,222-263`):

| Classfile Major Version | Java Release | Verifier Path | Failover to Type Inference | `jsr` / `ret` Allowed |
| :--- | :--- | :--- | :--- | :--- |
| `< 50` | JDK 1.1–5 | `inference_verify` directly | N/A | Yes |
| `50` (`STACKMAP_ATTRIBUTE_MAJOR_VERSION`) | JDK 6 | `ClassVerifier` (`StackMapTable`) | Yes (unless dumping static CDS archive) | Only via failover |
| `>= 51` (`NOFAILOVER_MAJOR_VERSION`) | JDK 7–27+ | `ClassVerifier` strictly | **No** (`can_failover == false`) | **No** (`VerifyError: Bad instruction`) |

In split verification, the compiler supplies a `StackMapTable` attribute encoding canonical type states (`locals[]`, `stack[]`, and `flags`) at every jump target, exception handler entry, and instruction immediately following an unconditional control-flow transfer (`no_control_flow == true`). `ClassVerifier::verify_stackmap_table` (`verifier.cpp:2056-2091`) walks bytecode in a single linear pass: whenever `this_offset == bci`, it checks that the abstractly executed `current_frame` is pointwise assignable to the declared table frame via `stackmap_table->match_stackmap(...)`, then replaces `current_frame` with the declared frame. Missing a frame after an unconditional transfer (`goto`, `athrow`, `return`) triggers `VerifyError: Expecting a stack map frame`; an out-of-order offset triggers `ClassFormatError: Bad stack map offset`. In the bytecode dispatch switch (`verifier.cpp:1909-1915`), `jsr`/`ret` hit `default:` and raise `VerifyError: Bad instruction`, eliminating subroutine polymorphism from verification.

#### Object Construction (`uninitialized` / `uninitializedThis`) and Larval Strict Fields
To prevent uninitialized object pointers from escaping or being read before constructor completion, `VerificationType` tracks two non-reference-assignable pre-initialization tokens (`verificationType.cpp:194-199`, `verifier.cpp:2507-2645`):

- `uninitialized(bci)`: pushed by `new` at bytecode offset `bci`. Upon `invokespecial <init>`, `verifier.cpp:2639-2644` verifies that offset `bci` actually holds `Bytecodes::_new`, then replaces all occurrences of `uninitialized(bci)` in locals and stack with the initialized class type.
- `uninitializedThis`: initial `local[0]` in every instance `<init>` method. Only `invokespecial <init>` on `current_class()` or `current_class()->super()` transforms `uninitializedThis` into `current_type()` (`verifier.cpp:2592-2638`). Exception handlers covering `<init>` replace `broken_type` (`uninitializedThis` if `<init>` fails) with `top` (`Bogus`) via `frame_in_exception_handler` (`verifier.cpp:2093-2117`), preventing `catch` blocks from observing a half-constructed `this`.
- **Early larval strict-field tracking**: At `verifier.cpp:2508-2514` and `1922-1925`, HotSpot permits `putfield` on `uninitializedThis` strictly for local fields of `current_class()`, tracking `fd.access_flags().is_strict()` so strict final fields (introduced for Valhalla/flexible constructor bodies) are verifiably initialized before `super.<init>()` runs.

#### The Interface Assignability Loophole (Deferred Runtime Checking)
A crucial, frequently misunderstood property of JVMS §4.10.1.2 and HotSpot's `VerificationType::resolve_and_check_assignability` (`verificationType.cpp:69-83`) is that **static bytecode verification does NOT verify interface implementation for non-array reference types**:

```cpp
// openjdk/jdk src/hotspot/share/classfile/verificationType.cpp:69-82
bool is_intf = target_klass->is_interface();
if (is_intf && (!from_field_is_protected ||
    from_name != vmSymbols::java_lang_Object())) {
  // For arrays, only allow assignability to Cloneable and Serializable.
  // Otherwise, we treat interfaces as java.lang.Object.
  return !from_is_array ||
    target_klass == vmClasses::Cloneable_klass() ||
    target_klass == vmClasses::Serializable_klass();
}
```

The rationale is historical and algorithmic: avoiding loading arbitrary interface hierarchies (and computing non-tree multiple-inheritance least upper bounds) during split verification. The concrete consequence for formal verification and bytecode consumers is sharp:

- **Live execution witness (OpenJDK 27.0.1, `-Xverify:all`)**: A synthesized classfile (`major_version = 65`, no `checkcast`) defines `public static Runnable coerceWithoutCast(Object o)` with bytecode `aload_0; areturn` and `public static void invokeWithoutCast(Object o)` with bytecode `aload_0; invokeinterface java/lang/Runnable.run:()V; return`. HotSpot verifies and loads both methods with **zero `VerifyError`**. Calling `Runnable forged = coerceWithoutCast("hello-not-runnable")` succeeds at runtime: `((Object) forged).getClass().getName()` reports `java.lang.String`, and `forged instanceof Runnable` evaluates to `false`. Only when an `invokeinterface` executes on `forged` (either `forged.run()` or `invokeWithoutCast`) does HotSpot's dynamic interface dispatch check throw `java.lang.IncompatibleClassChangeError: Class java.lang.String does not implement the requested interface java.lang.Runnable`.
- **Invariant consequence**: Any static analyzer or JIT pass operating on verified JVM bytecode **cannot assume** that a value statically typed as an interface `I` dynamically implements `I` until a runtime `checkcast`, `instanceof`, `aastore`, or `invokeinterface` succeeds on that value.

---

### 2. Generics Type Erasure, Synthetic Bridge Methods, and Covariant Array Store Checks

**Basis:** normative (JLS §4.6, §10.5, §10.10; JVMS `aastore`) + source (`openjdk/jdk` `TransTypes.java`, `objArrayKlass.cpp`, `refArrayKlass.cpp`) + execution (OpenJDK 27.0.1 `javac` + `javap -v` + `java`).

#### Type Erasure and Bridge Method Synthesis
Java generics are erased at bytecode generation (`com.sun.tools.javac.comp.TransTypes`): type variables erase to their leftmost bound (default `java.lang.Object`), and parameterized types erase to their raw class descriptor. Because JVM virtual dispatch (`invokevirtual` / `invokeinterface`) matches methods by exact `(name, erased_descriptor)` pair, a concrete override such as `StringBox.set(String)` (`(Ljava/lang/String;)V`) would **not** override `Box.set(Object)` (`(Ljava/lang/Object;)V`) in the vtable without compiler intervention.

`TransTypes.addBridge` (`src/jdk.compiler/share/classes/com/sun/tools/javac/comp/TransTypes.java:235-252`) resolves this by emitting a compiler-generated wrapper method flagged `ACC_BRIDGE | ACC_SYNTHETIC` (`0x1040`) bearing the supertype's erased descriptor `meth.erasure(types)`. Verified directly via `javap -v -p` on OpenJDK 27.0.1 for `class StringBox extends Box<String>`:

```text
void set(java.lang.Object);
  descriptor: (Ljava/lang/Object;)V
  flags: (0x1040) ACC_BRIDGE, ACC_SYNTHETIC
  Code:
    stack=2, locals=2, args_size=2
       0: aload_0
       1: aload_1
       2: checkcast     #13                 // class java/lang/String
       5: invokevirtual #19                 // Method set:(Ljava/lang/String;)V
       8: return
```

When caller code holds a raw or unchecked-cast `Box` reference (`Box raw = new StringBox(); raw.set(Integer.valueOf(7));`), virtual dispatch enters the bridge method, whose `checkcast java/lang/String` throws `ClassCastException` at the bridge line. Conversely, when a field or array is polluted through unchecked casts without passing through a bridge (e.g., `List<String>` containing an `Integer` via raw `List`), **no exception occurs at insertion**—heap pollution persists silently until a downstream consumer executes a compiler-inserted `checkcast` on read.

#### Covariant Reference Arrays and Runtime Store Checks
Unlike invariant generic containers (`List<String>` is not a subtype of `List<Object>`), Java reference arrays are **covariant**: if `S <: T`, then `S[] <: T[]`. HotSpot represents this directly in `ObjArrayKlass::compute_secondary_supers` (`objArrayKlass.cpp:330-352`) and `RefArrayKlass::allocate_klass` (`refArrayKlass.cpp:62-79`), wiring `S[]`'s super-klass to `T[]` and adding `Cloneable`, `Serializable`, and `elemSuper[]` as secondary supers.

Because `Object[] oa = new String[1]` is statically well-typed, every reference array element write (`aastore`) and bulk copy (`System.arraycopy` -> `RefArrayKlass::copy_array`, `refArrayKlass.cpp:123-161`) must dynamically check whether the runtime class of the stored element is a subtype of `RefArrayKlass::element_klass()`. Storing `Integer.valueOf(42)` into `oa[0]` throws `java.lang.ArrayStoreException: java.lang.Integer` (verified live on OpenJDK 27.0.1). Note that `RefArrayKlass::allocate_klass` (`refArrayKlass.cpp:64`) already enforces the Valhalla invariant `!props.is_null_restricted() || (n == 1 && element_klass->is_value_klass())`, foreshadowing null-restricted value arrays that add a runtime `NullPointerException` check on `aastore`.

---

### 3. Dynamic Class Redefinition (`java.lang.instrument`) vs. Speculative CHA Devirtualization

**Basis:** normative (JVMTI `RedefineClasses` / `java.lang.instrument`) + source (`openjdk/jdk` `dependencies.hpp`, `dependencies.cpp`, `jvmtiRedefineClasses.cpp`) + execution (OpenJDK 27.0.1 `-javaagent` + `-XX:+PrintCompilation`).

#### HotSpot Speculative `Dependencies` Taxonomy
Because the JVM supports dynamic class loading (`ClassLoader.defineClass`) and runtime bytecode replacement (`Instrumentation.redefineClasses` / `retransformClasses`), closed-world whole-program analysis is unsound without runtime invalidation guards. HotSpot's tiered compilers (C1/C2) therefore perform optimistic **Class Hierarchy Analysis (CHA)** and **method evolution assumptions** backed by explicit dependency records attached to each compiled `nmethod` (`src/hotspot/share/code/dependencies.hpp:105-160`):

| `Dependencies::DepType` | Recorded Assumption | Triggering Invalidation Event |
| :--- | :--- | :--- |
| `evol_method` | Compiled code used the exact bytecode contents of method `M` (self-compilation or inlining). | `JVMTI RedefineClasses` (`m->is_old()`) or breakpoint (`dependencies.cpp:1305-1315`). |
| `mismatch_calling_convention` | Method parameter scalarization / calling convention matches across super/sub methods. | Conflicting scalarized vs. non-scalarized override (`dependencies.cpp:1317-1324`). |
| `leaf_type` | Context class `CX` has no proper loaded subtypes. | Loading any subclass of `CX`. |
| `abstract_with_unique_concrete_subtype` | Abstract class `CX` has exactly one loaded concrete subtype `CC`. | Loading a second concrete subtype of `CX`. |
| `unique_concrete_method` | Under context `CX`, the concrete matching method set $MM(CX, M_1, RC_1, RM_1) \subseteq \{M_1\}$. | Loading a subclass overriding `M_1` (even via default interface method). |
| `unique_implementor` | Interface `CX` has a single concrete implementor class. | Loading a second implementor of `CX`. |
| `no_finalizable_subclasses` | No subclass of `CX` overrides `Object.finalize()`. | Loading a subclass with non-trivial finalizer. |
| `call_site_target_value` | `invokedynamic` `CallSite.target` equals a specific `MethodHandle`. | `CallSite.setTarget(...)` mutation. |

#### Structural Constraints of `JVMTI RedefineClasses`
`VM_RedefineClasses` (`src/hotspot/share/prims/jvmtiRedefineClasses.cpp:780-1228`) enforces strict binary compatibility constraints before allowing redefinition at a safepoint. Any attempt to violate these returns a dedicated JVMTI error (surfaced in Java as `UnsupportedOperationException`):

- **Forbidden**: Changing superclass or implemented interfaces (`JVMTI_ERROR_UNSUPPORTED_REDEFINITION_HIERARCHY_CHANGED`, lines 954–980); adding, removing, reordering, or changing types/modifiers of fields (`JVMTI_ERROR_UNSUPPORTED_REDEFINITION_SCHEMA_CHANGED`, lines 1036–1063); adding or deleting methods (`METHOD_ADDED`, lines 1193–1202; `METHOD_DELETED`, line 1228); changing class or method modifiers (`CLASS_MODIFIERS_CHANGED`, line 1017; `METHOD_MODIFIERS_CHANGED`, line 1159); changing key class attributes such as `NestHost`/`Record` incompatibly (`CLASS_ATTRIBUTE_CHANGED`, lines 780–912).
- **Permitted**: Replacing method bodies (bytecodes), constant pool entries, and attributes within existing methods.

#### Deoptimization Cascade on Redefinition
Even though class hierarchy edges cannot change during `RedefineClasses`, replacing a method body invalidates every compiled `nmethod` that compiled or **CHA-inlined** the old bytecode. `VM_RedefineClasses::flush_dependent_code()` (`jvmtiRedefineClasses.cpp:4144-4163`) handles this in two regimes at a safepoint:

1. **First redefinition without prior `evol` tracking (`!JvmtiExport::all_dependencies_are_recorded()`)**: Calls `CodeCache::mark_all_nmethods_for_evol_deoptimization(&deopt_scope)`—a **stop-the-world flush of the entire compiled code cache**, then flips `JvmtiExport::set_all_dependencies_are_recorded(true)`.
2. **Subsequent redefinitions (or when a `-javaagent` with `Can-Redefine-Classes: true` enabled tracking at startup)**: Calls `CodeCache::mark_dependents_for_evol_deoptimization(&deopt_scope)`, walking only `nmethod`s with an `evol_method` dependency whose `Method::is_old()` is now true (`dependencies.cpp:1310`), marking them `not entrant`, and triggering stack-frame deoptimization (`deopt_scope.deoptimize_marked()`).

**Live execution witness (OpenJDK 27.0.1)**: Running `RedefDriver.hotCaller(Target, 1000)` under `-javaagent:redef-agent.jar -XX:+PrintCompilation -Xlog:redefine+class+nmethod=debug` compiled `Target::compute` (4 bytes, `x + 1`) at C2 tier 4 (`compile_id=213`) and OSR-compiled `RedefDriver::hotCaller` at C2 tier 4 (`compile_id=216 %`) with `Target::compute` devirtualized and inlined (`BEFORE_REDEFINE: 500500`). Invoking `Instrumentation.redefineClasses` to replace `Target::compute` with `x + 1000` (6 bytes) immediately logged:
- `Found evol dependency of nmethod Target.compute((I)I) compile_id=213`
- `Found evol dependency of nmethod RedefDriver.hotCaller((LTarget;I)I) compile_id=216`
- `Marked dependent nmethods for deopt` -> `compile_id=213`, `215`, `216 %` all `made not entrant: marked for deoptimization`
- Subsequent calls recompiled both methods (`compile_id=237/239`, `238 %/240`) and produced `AFTER_REDEFINE: 1499500`.

---

### 4. Manson–Pugh–Adve JMM Causality, Out-of-Thin-Air Defects, and `VarHandle` Modes

**Basis:** normative (JLS §17.4, JEP 193) + source (`openjdk/jdk` `VarHandle.java`) + derived (Manson–Pugh–Adve POPL 2005; Ševčík–Aspinall ECOOP 2008; Batty et al. ESOP 2015; Kang et al. POPL 2017) + execution (formal Python causality probe).

#### Why Happens-Before Alone Fails (Out-of-Thin-Air Values)
Java guarantees memory and type safety **even for programs containing data races** (unlike C/C++/Rust where data races are undefined behavior). A pure happens-before memory model (HBMM)—requiring only that no read sees a write that happens-after it or is overwritten by an intervening happens-before write—is **unsound for Java's security model** because it permits **out-of-thin-air (`OOTA`)** values. In **Causality Test Case 4 (TC4)** (initial `x = 0, y = 0`):

```text
Thread 1: r1 = x; y = r1;    ||    Thread 2: r2 = y; x = r2;
```

Under HBMM, `r1 = 42, r2 = 42` is consistent because `T1`'s read of `x` does not happen-before `T2`'s write `x = 42`, and `T2`'s read of `y` does not happen-before `T1`'s write `y = 42`. Such self-justifying cycles could forge arbitrary object references or breach sandbox invariants in untrusted bytecode.

#### JLS §17.4.8 Iterative Justification Chains
Manson, Pugh, and Adve (POPL 2005, DOI `10.1145/1040305.1040336`) defined JMM causality by requiring a well-formed execution $E = \langle P, A, \text{po}, \text{so}, W, V, \text{sw}, \text{hb} \rangle$ to be constructed incrementally via a sequence of well-formed justifying executions $E_1, E_2, \dots, E_k = E$ and monotonically growing committed action sets $\emptyset = C_0 \subseteq C_1 \subseteq \dots \subseteq C_k = A$ obeying nine structural constraints (JLS §17.4.8). Crucially:

1. **Happens-before restriction on uncommitted reads (Rule 4)**: Every read $r \in A_i \setminus C_{i-1}$ in justifying execution $E_i$ must see a write $W_i(r)$ that **happens-before** $r$ in $E_i$ ($W_i(r) \xrightarrow{\text{hb}_i} r$).
2. **Commitment stability (Rules 5–7)**: Once a read $r$ is committed in $C_i$, its read-from write in $E_i$ must already have been committed in $C_{i-1}$ ($W_i(r) \in C_{i-1}$), and for all $j \ge i$, $W_j(r) = W_i(r)$ (or for newly committed reads in $C_i \setminus C_{i-1}$, their final write $W(r) \in C_{i-1}$ is fixed in $E_{i+1}$).

**Formal execution probe results**:
- **TC4 (`r1 = x; y = r1 || r2 = y; x = r2`)**: Starting from $C_0 = \{\text{init } x=0, \text{init } y=0\}$, Rule 4 forces every uncommitted read in $E_1$ to observe `0`; hence the least fixed point of justifiable values is $\{0\}$ only, **forbidding** `r1 = r2 = 42`.
- **TC1 (`r1 = x; if (r1 >= 0) y = 1 || r2 = y; x = r2`)**: Because `x` is never negative in any execution, in $E_1$ `r1` reads `init x = 0`, `0 >= 0` holds, and `T1` commits `y = 1` into $C_1$. In $E_2$, `r2` reads committed `y = 1` and `T2` commits `x = 1` into $C_2$. In $E_3$, `r1` reads committed `x = 1`, justifying **`r1 = r2 = 1`** (permitting cross-thread range analysis + reordering of `y = 1` before `r1 = x`).
- **TC5 (`r1=x; y=r1 || r2=y; x=r2 || z=1 || r3=z; x=r3`)**: Even though `T3` and `T4` *could* write `x = 1` in another execution, outcome `r1 = 1, r2 = 1, r3 = 0` is **forbidden** because committing `T4: x = 1` in $E_1$ violates commitment stability when `T4` actually writes `x = 0` in the final execution $E$.

#### Structural Defects of JMM Causality
Subsequent formal verification exposed four fundamental defects in JLS §17.4.8:

| Defect Class | Primary Literature | Concrete Failure / Implication |
| :--- | :--- | :--- |
| **Unsoundness of standard compiler optimizations** | Ševčík & Aspinall, ECOOP 2008 (`10.1007/978-3-540-70592-5_3`) | **Redundant read-after-read elimination** (`r1 = x; r2 = x` $\to$ `r1 = x; r2 = r1`), **irrelevant read introduction**, and **roach-motel** code motion (moving accesses into `synchronized` blocks) can introduce behaviors forbidden by JMM causality on the unoptimized source—breaking the JMM's core goal of validating standard JIT optimizations. |
| **Undecidability of causality checking** | Botinčan, Glavan & Runje (2010); Aspinall & Ševčík (2007) | Deciding whether a finite execution satisfies JLS §17.4.8 is **undecidable** in general because justifying executions $E_i$ can require checking termination of arbitrary sequential subprograms $S$ (`y = x || S; x = 1`) and $\omega$-order restrictions on `so` interact anomalously with infinitely many volatile initializations. |
| **Impossibility of thin-air-free local axiomatic repair** | Batty, Memarian, Nienhuis, Pichon-Pharabod & Sewell, ESOP 2015 (`10.1007/978-3-662-46669-8_12`) | Proved that no purely per-execution axiomatic memory model over single candidate executions (like C++11's `mo_relaxed`) can simultaneously forbid OOTA and allow all standard compiler optimizations without either multi-execution semantics or operational promises. |
| **Operational replacement via promises** | Kang, Hur, Lahav, Vafeiadis & Dreyer, POPL 2017 (`10.1145/3009837.3009850`) | Replaced JMM justifying chains with **promising semantics**, where a thread may promise a future write only if it can **certify** fulfilling that promise thread-locally from the current memory state, validating standard optimizations while prohibiting OOTA. |

#### Practical JDK 9+ Memory Ordering (`java.lang.invoke.VarHandle`)
Rather than rewriting JLS §17.4.8's causality formalism, JDK 9 (JEP 193) introduced `VarHandle` with four layered memory-ordering modes (`src/java.base/share/classes/java/lang/invoke/VarHandle.java:115-165`):

| `VarHandle` Mode | Bitwise Atomicity | Same-Variable Coherence | Cross-Variable Ordering | Relation to JLS §17.4 / C++11 |
| :--- | :--- | :--- | :--- | :--- |
| **Plain** (`get`/`set`) | Refs & primitives $\le 32$ bits only (`long`/`double` may word-tear per JLS §17.7) | None (compiler may hoist/coalesce) | None | Ordinary Java field access |
| **Opaque** (`getOpaque`/`setOpaque`) | **Yes** (including 64-bit `long`/`double`) | **Yes** (per-variable coherence + progress/no loop hoisting) | None (no causal/hb edge; no OOTA guarantee formally specified beyond coherence) | Stronger than C++ `mo_relaxed` on progress/coherence |
| **Acquire / Release** (`getAcquire`/`setRelease`) | **Yes** | **Yes** | Release-write $\xrightarrow{\text{sw}}$ Acquire-read pairs order prior writes before subsequent reads | Matches C++ `mo_acquire` / `mo_release` |
| **Volatile** (`getVolatile`/`setVolatile`) | **Yes** | **Yes** | Total global order across all volatile accesses + Acquire/Release | Matches Java `volatile` / C++ `mo_seq_cst` |

---

### 5. Project Valhalla Value-Object Memory Layouts and Atomicity / Tearing Boundaries

**Basis:** normative draft (JEP 401) + source (`openjdk/valhalla` `lworld` commit `12e87d09246d366cc74cb409e4c914351256e98b`: `layoutKind.hpp`, `fieldLayoutBuilder.cpp`, `LooselyConsistentValue.java`, `NullRestricted.java`).

#### The Six HotSpot `LayoutKind` Encodings
Value classes (`value class`) relinquish object identity (no monitor lock, `==` compares state, fields are implicitly `final`), allowing HotSpot to **scalarize** instances in registers across call boundaries and **flatten** them inline inside enclosing objects and arrays. However, flattening multi-word value objects into shared mutable fields creates a direct tension with JLS §17.7's reference-atomicity guarantee: a reference write updates an entire object atomically via one pointer store, whereas overwriting multiple flattened subfields non-atomically under a data race causes **tearing**—producing a value whose fields never coexisted in any constructor invocation.

In `openjdk/valhalla` (`src/hotspot/share/oops/layoutKind.hpp:88-96`), HotSpot encodes this exact atomicity/nullability matrix via six `LayoutKind` values:

| `LayoutKind` (Enum Value) | Null Marker | Access Atomicity | Permitted Field/Container Context | Tearing Possible Under Data Race? |
| :--- | :--- | :--- | :--- | :--- |
| `REFERENCE` (`0`) | Heap pointer `nullptr` | Single pointer load/store (**atomic**) | Any value field (`volatile`, `static`, oversized, or fallback) | **No** |
| `BUFFERED` (`1`) | Reserved slot in payload (unused while buffered) | N/A (standalone immutable heap object) | Standalone heap-allocated value instances; aligned compatibly with all flat layouts | **No** (immutable after publication) |
| `NULL_FREE_NON_ATOMIC_FLAT` (`2`) | None (null-restricted) | **Non-atomic** (subfields read/written independently) | `@NullRestricted` field whose value class is `@LooselyConsistentValue` (or naturally atomic, e.g., single $\le$ word field) | **Yes** (unless naturally atomic) |
| `NULL_FREE_ATOMIC_FLAT` (`3`) | None (null-restricted) | **Atomic** (hardware single-instruction width; alignment == size) | `@NullRestricted` field of atomic (default) value class fitting atomic width | **No** |
| `NULLABLE_ATOMIC_FLAT` (`4`) | 1-byte null marker (`0` = null, non-`0` = non-null) | **Atomic** (payload + null marker updated in one atomic op) | Default JEP 401 nullable value field when size+marker fits atomic width & `UseNullableAtomicValueFlattening` | **No** |
| `NULLABLE_NON_ATOMIC_FLAT` (`5`) | 1-byte null marker | **Non-atomic** | **Strict `final` non-static fields only** (initialized before `super()`, never mutated afterward) or empty value classes | **No** (no concurrent write possible after construction) |

#### Nullable Flat Reset Protocol and Container-to-Field Tearing Prevention
Two non-obvious implementation invariants in `openjdk/valhalla` (`layoutKind.hpp:49-80`, `fieldLayoutBuilder.cpp:45-105`) directly govern soundness and verification:

1. **Oop-Leak Prevention on `putfield null` (`NULLABLE_ATOMIC_FLAT`)**: Setting a `NULLABLE_ATOMIC_FLAT` field to `null` cannot merely zero the 1-byte null marker if the value payload contains object references (oops), because stale oops would retain garbage until overwritten. HotSpot therefore pre-allocates a dedicated all-zero **reset value instance** for each value class supporting `NULLABLE_ATOMIC_FLAT` (distinct from the default value instance, whose null marker byte may be toggled non-zero during copies) and atomically overwrites the entire flat field with zeros (`layoutKind.hpp:63-69`).
2. **Container-to-Field Tearing Contamination Guard (`can_use_atomic_flat`)**: In `fieldLayoutBuilder.cpp:45-105`, HotSpot refuses to use `NULL_FREE_ATOMIC_FLAT`, `NULLABLE_ATOMIC_FLAT`, or `NULLABLE_NON_ATOMIC_FLAT` when laying out a field inside a `@LooselyConsistentValue` container (`can_use_atomic_flat == false`):
   - *Reason*: Even if field `F`'s class `Inner` did **not** opt into `@LooselyConsistentValue`, tearing the enclosing `Outer` value under a data race could tear `Inner`'s bytes—or decouple `Inner`'s null marker from its payload. HotSpot therefore forces `Inner` back to `LayoutKind::REFERENCE` inside a loosely consistent container (unless `Inner` is itself naturally atomic and null-free).
   - Similarly, `volatile` and `static` value fields always fall back to `LayoutKind::REFERENCE` (`fieldLayoutBuilder.cpp:58-66`), and a per-container byte `budget` (`adjust_with_budget`, lines 107–120) bounds total inline expansion before reverting remaining fields to `REFERENCE`.

#### Tearing Failure Mode (`@LooselyConsistentValue`)
As documented directly in `jdk/internal/vm/annotation/LooselyConsistentValue.java:30-42`:
> *"A loosely-consistent value class is a class that is willing to tolerate data corruption when fields or arrays storing instances of the class are updated under race. Specifically, a value object read from such a field may contain combinations of field values that were never set by a previous constructor invocation."*

Example failure mode: A `value class DateRange(int start, int end)` enforcing `start <= end` in its constructor is **safe** under default JEP 401 semantics (`NULLABLE_ATOMIC_FLAT` / `REFERENCE`): racing writes of `DateRange(1, 5)` and `DateRange(10, 20)` can observe only `(1, 5)` or `(10, 20)`. If annotated `@LooselyConsistentValue` and stored in a `@NullRestricted` field/array (`NULL_FREE_NON_ATOMIC_FLAT`), a data race can observe **`DateRange(10, 5)`**, violating the constructor's representation invariant (`start <= end`) in pure Java without `Unsafe`!

---

### 6. Project Loom Virtual-Thread Continuation Freezing and Carrier Pinning (JEP 444 vs. JEP 491)

**Basis:** normative (JEP 444, JEP 491) + source (`openjdk/jdk` `Continuation.java`, `VirtualThread.java`, `continuationFreezeThaw.cpp`, `objectMonitor.cpp`) + execution (OpenJDK 27.0.1 JFR `jdk.VirtualThreadPinned`).

#### Continuation Stack Freezing Architecture
Virtual threads (`java.lang.VirtualThread`) multiplex lightweight user-mode tasks onto a ForkJoinPool of OS carrier threads by running inside a `jdk.internal.vm.Continuation` (`VThreadContinuation`, `VirtualThread.java:236-257`). When a virtual thread blocks on a Loom-aware operation (e.g., `LockSupport.park`, `SocketChannel`, `ReentrantLock`, or—in JDK 24+—`synchronized` monitor contention and `Object.wait`), HotSpot executes `ContinuationFreezeThaw` (`continuationFreezeThaw.cpp:1960-2073`), copying the Java frames between the current top frame and `ContinuationEntry` out of the carrier OS stack into a GC-managed heap `StackChunk` (`freeze_fast` / `freeze_slow`) and unmounting the virtual thread so the carrier immediately executes another virtual thread.

#### Evolution of Carrier Pinning: JDK 21–23 vs. JDK 24+ (JEP 491)
A major behavioral transition separates JDK 21–23 from JDK 24+ (including `openjdk/jdk` HEAD and OpenJDK 27.0.1):

| Blocking Condition on Virtual Thread | JDK 21–23 (JEP 444) | JDK 24–27+ (JEP 491) | Underlying HotSpot Mechanism (`openjdk/jdk` HEAD) |
| :--- | :--- | :--- | :--- |
| Blocking (`park`/`sleep`/I/O) inside `synchronized` block | **PINS carrier** (`Pinned.MONITOR`) | **Unmounts cleanly** (no pin) | Monitor ownership stored by virtual thread identity (`owner_id`), not carrier `JavaThread*`; frames freeze cleanly while holding inflated `ObjectMonitor`. |
| Contending on `monitorenter` / calling `Object.wait()` | **PINS carrier** (`Pinned.MONITOR`) | **Unmounts cleanly** (no pin) | `objectMonitor.cpp:133-160`: contending vthread freezes frames to heap, CAS-pushes onto `entry_list`, returns to Java unmount path; exiting thread pushes wakee to `_vthread_list_head` and unparks the dedicated unblocker thread for competitive handoff. |
| Native JNI / Panama FFM upcall frame on stack | **PINS carrier** (`Pinned.NATIVE`) | **STILL PINS carrier** (`Pinned.NATIVE`) | `continuationFreezeThaw.cpp:2052-2055`: `is_pinned0` walks frames; any `is_native()` or `is_native_frame()` returns `freeze_pinned_native` because arbitrary C stack pointers/ABI frames cannot be relocated to a heap `StackChunk`. |
| Blocking inside class initializer (`<clinit>`) or VM critical section | **PINS carrier** | **STILL PINS carrier** (`Pinned.NATIVE` / `Pinned.CRITICAL_SECTION`) | VM `InstanceKlass::initialize_impl` places a native VM C++ frame on the carrier stack (and `Continuation.pin()` sets `entry->is_pinned()`, returning `freeze_pinned_cs`, `continuationFreezeThaw.cpp:1968-1982`). |
| OOME / StackOverflow during freeze | **PINS carrier** | **STILL PINS carrier** (`Pinned.EXCEPTION`) | `Continuation.java:58-62`: `Pinned { NATIVE, CRITICAL_SECTION, EXCEPTION }`. |

Notice that in `openjdk/jdk` (`src/java.base/share/classes/jdk/internal/vm/Continuation.java:58-62`), **`Pinned.MONITOR` has been completely removed** from the `Pinned` enum:
```java
public enum Pinned {
    /** Native frame on stack */ NATIVE,
    /** In critical section */   CRITICAL_SECTION,
    /** Exception (OOME/SOE) */  EXCEPTION
}
```

**Live execution witness (OpenJDK 27.0.1, JFR `jdk.VirtualThreadPinned`)**:
Running `LoomPinningProbe` with JFR recording `jdk.VirtualThreadPinned` enabled:
- **Test A (`synchronized` contention + `Thread.sleep` inside `synchronized`)**: Two virtual threads (`vt-sync-holder` holding `LOCK` across a 40ms `Thread.sleep`, `vt-sync-contender` contending on `LOCK` and sleeping 20ms) emitted **0 `jdk.VirtualThreadPinned` events**.
- **Test B (blocking inside static class initializer `<clinit>`)**: `vt-clinit` triggering `BlockingClinit.<clinit>` and awaiting a `CountDownLatch` for 30ms emitted **1 `jdk.VirtualThreadPinned` event** (`thread=vt-clinit, duration_ms=30.332584, frames=[VirtualThread.postPinnedEvent, VirtualThread.parkOnCarrierThread, VirtualThread.park, ...]`), confirming that native VM frames on the call stack still pin the OS carrier thread and can starve the carrier pool if a virtual thread blocks on a lock or I/O inside `<clinit>` or a JNI/FFM upcall.

---

### 7. Project Panama FFM Confined and Shared `Arena` Temporal Safety

**Basis:** normative (JEP 454, JDK 22+) + source (`openjdk/jdk` `MemorySessionImpl.java`, `ConfinedSession.java`, `SharedSession.java`, `scopedMemoryAccess.cpp`) + execution (OpenJDK 27.0.1).

#### Memory Session State Machine and Zero-Sync Hot-Path Check
The Foreign Function & Memory (FFM) API (`java.lang.foreign`) eliminates use-after-free and spatial out-of-bounds bugs for off-heap memory without per-access mutexes or atomic reference counting on every load/store. Every `MemorySegment` references a `MemorySessionImpl` (`sealed class`, permitting `ConfinedSession`, `SharedSession`, and `GlobalSession`, `MemorySessionImpl.java:56-86`):

- **Monotonic state field**: `@Stable int state` takes values `OPEN = 0`, `CLOSED = -1`, or `NONCLOSEABLE = 1`. Because `OPEN -> CLOSED` is one-way and `NONCLOSEABLE` (`GLOBAL_SESSION`, heap sessions) never transitions, HotSpot C2 constant-folds liveness checks on global/heap segments away completely.
- **Monomorphic plain-mode hot path (`MemorySessionImpl.checkValidStateRaw`, lines 198–206)**:
  ```java
  @ForceInline
  public void checkValidStateRaw() {
      if (owner != null && owner != Thread.currentThread()) {
          throw WRONG_THREAD; // pre-allocated ScopedAccessError -> WrongThreadException
      }
      if (state < OPEN) {
          throw ALREADY_CLOSED; // pre-allocated ScopedAccessError -> IllegalStateException
      }
  }
  ```
  Critically, **neither `ConfinedSession` nor `SharedSession` uses a volatile read or memory barrier inside `checkValidStateRaw()`**!

#### `Arena.ofConfined()` vs. `Arena.ofShared()` Reclamation Protocols

| Arena Kind | Backing Session | Thread Access | `close()` Synchronization Mechanism | Concurrent Access-vs-Close Safety |
| :--- | :--- | :--- | :--- | :--- |
| `Arena.ofConfined()` | `ConfinedSession` (`owner = creator`) | Single owner thread only (`WrongThreadException` otherwise) | Plain `state = CLOSED` after checking `acquireCount - asyncReleaseCount == 0` (`ConfinedSession.java:74-83`). | Trivial by single-thread confinement (no cross-thread access possible). |
| `Arena.ofShared()` | `SharedSession` (`owner = null`) | Any thread concurrently | 1. CAS `ACQUIRE_COUNT: 0 -> -1` (`SharedSession.java:84-89`); 2. `STATE.setVolatile(this, CLOSED)` (line 91); 3. `SCOPED_MEMORY_ACCESS.closeScope(this, ALREADY_CLOSED)` (line 92) -> **HotSpot Thread-Local Handshake**; 4. `resourceList.cleanup()` (`free`/`munmap`). | Guaranteed deterministic UAF freedom via two-phase handshake + async exception + C2 frame deoptimization. |
| `Arena.ofAuto()` | `ImplicitSession` (`extends SharedSession`) | Any thread concurrently | Non-closeable explicitly (`UnsupportedOperationException`); freed by `java.lang.ref.Cleaner` only when GC proves unreachable. | Guaranteed by GC reachability (non-deterministic deallocation). |
| `Arena.global()` | `GlobalSession` (`state = NONCLOSEABLE`) | Any thread concurrently | Never closed (`UnsupportedOperationException`). | Trivial (unbounded lifetime). |

#### Deep Dive: HotSpot's `ScopedMemoryAccess_closeScope` Handshake Protocol
Why is a plain-mode `state < OPEN` check sound for `SharedSession` when Thread A reads off-heap memory in a tight C2-compiled loop while Thread B calls `sharedArena.close()`? Inspection of `src/hotspot/share/prims/scopedMemoryAccess.cpp:42-317` reveals a two-branch runtime verification protocol executed by `ScopedMemoryAccess_closeScope` **before** `resourceList.cleanup()` frees the native buffer:

1. **Global Thread-Local Handshake (`Handshake::execute(&cl)`, line 307)**: Synchronizes the closing thread with every running `JavaThread`, establishing cross-thread memory visibility of `STATE = CLOSED` (eliminating the need for acquire barriers on the reader hot path) and pausing/inspecting each thread's stack via `CloseScopedMemoryHandshakeClosure::do_thread` (lines 180–268).
2. **Branch A — Thread is inside an `@Scoped` memory-access method (`is_accessing_session`, lines 94–118, 195–209)**: Walks Java frames inside `java.base` (or the entire stack if JVMTI agents are loaded, lines 58–69) checking `m->is_scoped()` and scanning frame locals for `oop == session`. Because `do_thread` may execute asynchronously while the target is in native code, it cannot throw directly; instead it increments `Atomic<int> async_exceptions` and installs a self-processed **`ScopedAsyncExceptionHandshakeClosure`** via `jt->install_async_exception(...)` (lines 135–166, 209). Back in `ScopedMemoryAccess_closeScope` (lines 312–316), the closing thread **blocks in a `SpinYield` loop (`while (async_exceptions.load_acquire() > 0)`)** until every in-flight reader processes its async handshake and unwinds out of the `@Scoped` access—guaranteeing `free()`/`munmap()` never races with an active memory instruction!
3. **Branch B — C2 strip-mined loop hoisting (`!in_scoped`, lines 210–266)**: C2 may inline `@Scoped` accesses into a loop and hoist `checkValidStateRaw()` out of a strip-mined inner loop, placing a safepoint poll *outside* `@Scoped` yet *between* the hoisted liveness check and a subsequent memory instruction. When `last_frame.is_compiled_frame()` and `code->has_scoped_access() && is_session_live(last_frame, register_map)` (scanning frame oops and nmethod oops via `OopFinder`), HotSpot calls **`Deoptimization::deoptimize(jt, last_frame)`** (line 261), forcing the thread back to the interpreter so it re-executes `checkValidStateRaw()` before touching memory again!
4. **Native-Call Pinning (`whileAlive` / `acquire0`)**: Because C functions invoked through `Linker.downcallHandle` do not have Java safepoints or `@Scoped` checks, FFM downcalls acquire the session (`acquire0()` incrementing `ACQUIRE_COUNT`) for the duration of the native call; `SharedSession.justClose()` rejects closing with `IllegalStateException: Session is acquired by N clients` while any downcall holds it (`SharedSession.java:87-89`).
5. **Restricted Escape Hatch**: `MemorySegment.reinterpret(long newSize, Arena arena, Consumer<MemorySegment> cleanup)` is a **restricted** method (requiring `--enable-native-access=<module>` to suppress warnings/errors) because binding a raw C pointer's spatial bounds and temporal lifetime relies on programmer-supplied native invariants outside the JVM's verification boundary.

**Live execution witness (OpenJDK 27.0.1)**: `PanamaArenaSafety` confirmed:
- `Arena.ofConfined()`: owner read `0x1122334455667788`; other thread threw `java.lang.WrongThreadException: Attempted access outside owning thread`; owner post-close read threw `java.lang.IllegalStateException: Already closed`.
- `Arena.ofShared()`: background thread continuously reading a 1024-`long` off-heap segment completed `3239` reads before the main thread called `shared.close()`, whereupon the reader deterministically unwound with `java.lang.IllegalStateException: Already closed` and zero native faults.

---

### 8. Cross-Subsystem Verification and FFI Boundary Matrix

**Basis:** derived (synthesizing Findings 1–7).

| Subsystem / Boundary | Static Enforcement | Dynamic / Runtime Enforcement | Escape / Failure Mode | Impact on Formal Verification / FFI |
| :--- | :--- | :--- | :--- | :--- |
| Bytecode Verification (`v >= 51`) | `StackMapTable` linear type check (`ClassVerifier`) | `invokeinterface`, `checkcast`, `aastore` | Interface types unchecked statically (`verificationType.cpp:74-82`) | Bytecode verifiers/JITs must NOT assume interface-typed locals implement the interface before a runtime check. |
| Generics & Arrays | `javac` type checker + erasure | Bridge `checkcast` (`ClassCastException`); `aastore` (`ArrayStoreException`) | Raw-type heap pollution fails lazily on read | Erased signatures cannot be trusted for element/parameter types across untyped/reflective/JNI callers. |
| CHA Devirtualization vs. `Instrumentation` | None (open-world JVM) | `Dependencies` (`evol_method`, `leaf_type`, `unique_concrete_method`) + safepoint deopt | First unmonitored redefinition flushes entire code cache | Ahead-of-time closed-world devirtualization is invalid unless `Can-Redefine-Classes` & dynamic classloading are disabled. |
| JMM Causality & `VarHandle` | None (data races are legal Java) | Hardware fences (`Opaque`/`Acquire`/`Release`/`Volatile`) | JMM causality invalidates RRE/roach-motel; plain `long`/`double` tear | Verified concurrent algorithms should target explicit `VarHandle` Acquire/Release/Volatile or DRF-SC rather than JLS §17.4.8 causality proofs. |
| Valhalla Value Layouts | `value class`, strict finals, `@NullRestricted` | `LayoutKind` selection; null-marker + atomic hardware ops | `@LooselyConsistentValue` allows multi-field tearing breaking constructor invariants | Never attach `@LooselyConsistentValue` to types carrying cross-field safety/bounds invariants. |
| Loom Virtual Threads | None statically | `ContinuationFreezeThaw` (`is_pinned0`), JFR `VirtualThreadPinned` | Native JNI/FFM upcall frames and `<clinit>` still pin OS carriers (even post-JEP 491) | Blocking inside JNI/FFM upcalls or `<clinit>` risks carrier-pool deadlock under high virtual-thread concurrency. |
| Panama FFM `Arena` | `Arena` API + `--enable-native-access` for restricted ops | Plain-mode `checkValidStateRaw()` + `ScopedMemoryAccess_closeScope` handshake & C2 deopt | `MemorySegment.reinterpret` & unguarded native pointers outside `Arena` lifecycle | Temporal safety holds for pure Java accesses and downcall-acquired segments; raw pointer retention inside C libraries escapes FFM enforcement. |

## Boundaries

- **Known not to apply**:
  - **Loom `synchronized` carrier pinning**: Known **not** to apply to JDK 24+ (JEP 491; verified directly in `openjdk/jdk` `186489b55b5df61e270174a76104a2af27cc7197` and by live JFR execution on OpenJDK 27.0.1). Still applies to JDK 21–23.
  - **Default Valhalla value-object tearing**: Known **not** to apply to standard JEP 401 value classes without `@LooselyConsistentValue`; HotSpot enforces tearing-free updates via `NULLABLE_ATOMIC_FLAT` / `NULL_FREE_ATOMIC_FLAT` / `REFERENCE` and blocks atomic-flat embedding inside loosely consistent containers (`fieldLayoutBuilder.cpp:45-105`).
  - **Static interface verification**: Known **not** to be enforced by HotSpot's `StackMapTable` verifier for non-array reference types (`verificationType.cpp:74-82`, confirmed under `-Xverify:all`).
- **Not examined**:
  - **Compiled Valhalla binary execution**: No prebuilt `openjdk/valhalla` `lworld` JDK binary was installed on the execution host; Valhalla findings are backed by direct source inspection of `openjdk/valhalla` commit `12e87d09246d366cc74cb409e4c914351256e98b`, not runtime execution of `lworld` binaries.
  - **JNI upcall pinning execution & C2 assembly inspection**: Native pinning was executed via VM `<clinit>` (`LoomPinningProbe`) and verified in `continuationFreezeThaw.cpp:2052-2055`; compiling a custom shared-library JNI callback via `gcc` to emit a second `Pinned.NATIVE` trace and inspecting emitted C2 x86-64/AArch64 assembly for `ScopedMemoryAccess` strip-mined loops were not executed.
  - **Non-HotSpot JVMs**: GraalVM Native Image (closed-world AOT), Eclipse OpenJ9, and Android ART were not examined; their verifier edge cases, CHA assumptions, and memory/FFI models differ from HotSpot.
  - **JEP 401 final Java SE specification text**: Because JEP 401 remains in preview/development on `openjdk/valhalla`, final language syntax for null-restricted types (`T!`) and public tearing opt-in syntax (vs. internal `@LooselyConsistentValue` / `@NullRestricted`) are **unknown** until JEP finalization.
- **Unsupported**:
  - **Adding/removing fields or changing inheritance hierarchies via `Instrumentation.redefineClasses`**: Explicitly unsupported by HotSpot (`JVMTI_ERROR_UNSUPPORTED_REDEFINITION_SCHEMA_CHANGED` / `HIERARCHY_CHANGED`).
  - **Closing `Arena.ofAuto()` or `Arena.global()` explicitly**: Explicitly unsupported (`UnsupportedOperationException`).
  - **Deterministic JMM causality verification of arbitrary Java programs**: Proven undecidable in general (Botinčan, Glavan & Runje); no general decision procedure exists.
- **Attractive stronger conclusions NOT established**:
  - Panama `Arena.ofShared()` does **not** protect against a C library caching a raw `MemorySegment.address()` pointer beyond the duration of a downcall and dereferencing it after `Arena.close()`; temporal safety covers Java-side accesses and `acquire0()`-scoped downcalls only.
  - Passing `java -Xverify:all` does **not** imply full nominal type safety of all verified locals at bytecode level (due to the interface assignability deferral documented in Finding 1).

## Evidence

### Upstream Git Source Inspections (Observed 2026-11-19)

| Repository & Commit | File Path | Symbols / Line Ranges | Role |
| :--- | :--- | :--- | :--- |
| `openjdk/jdk` `186489b55b5df61e270174a76104a2af27cc7197` | `src/hotspot/share/classfile/verifier.hpp` | `STACKMAP_ATTRIBUTE_MAJOR_VERSION = 50` (L62) | source |
| `openjdk/jdk` `186489b55b5df61e270174a76104a2af27cc7197` | `src/hotspot/share/classfile/verifier.cpp` | `NOFAILOVER_MAJOR_VERSION = 51` (L68); `Verifier::verify` (L221–280); `jsr`/`ret` rejection (L1909–1925); `verify_stackmap_table` & `verify_exception_handler_targets` (L2056–2142); `uninitializedThis` / strict-field `putfield` (L2507–2644) | source |
| `openjdk/jdk` `186489b55b5df61e270174a76104a2af27cc7197` | `src/hotspot/share/classfile/verificationType.cpp` | `resolve_and_check_assignability` interface-as-`Object` rule (L54–98); `is_reference_assignable_from` (L100–143) | source |
| `openjdk/jdk` `186489b55b5df61e270174a76104a2af27cc7197` | `src/jdk.compiler/share/classes/com/sun/tools/javac/comp/TransTypes.java` | `addBridge` (`SYNTHETIC \| BRIDGE`, L235–252), `addBridgeIfNeeded` (L323–330) | source |
| `openjdk/jdk` `186489b55b5df61e270174a76104a2af27cc7197` | `src/hotspot/share/oops/objArrayKlass.cpp`, `refArrayKlass.cpp` | `compute_secondary_supers` (L330–352), `JVM_ACC_IDENTITY` (L399); `RefArrayKlass::copy_array` `ArrayStoreException` (L62–161) | source |
| `openjdk/jdk` `186489b55b5df61e270174a76104a2af27cc7197` | `src/hotspot/share/code/dependencies.hpp`, `dependencies.cpp` | `enum DepType` (L105–160); `check_evol_method`, `check_mismatch_calling_convention`, `find_unique_concrete_method` (L1305–1435) | source |
| `openjdk/jdk` `186489b55b5df61e270174a76104a2af27cc7197` | `src/hotspot/share/prims/jvmtiRedefineClasses.cpp` | Unsupported redefinition error checks (L780–1228); `VM_RedefineClasses::flush_dependent_code` (L4144–4163) | source |
| `openjdk/jdk` `186489b55b5df61e270174a76104a2af27cc7197` | `src/java.base/share/classes/java/lang/invoke/VarHandle.java` | Access mode memory-ordering contract: Plain, Opaque, Acquire/Release, Volatile (L115–165) | documentation + source |
| `openjdk/jdk` `186489b55b5df61e270174a76104a2af27cc7197` | `src/java.base/share/classes/jdk/internal/vm/Continuation.java`, `java/lang/VirtualThread.java` | `enum Pinned { NATIVE, CRITICAL_SECTION, EXCEPTION }` (L58–62); `VThreadContinuation`, `runContinuation` (L236–280) | source |
| `openjdk/jdk` `186489b55b5df61e270174a76104a2af27cc7197` | `src/hotspot/share/runtime/continuationFreezeThaw.cpp`, `objectMonitor.cpp` | `freeze_pinned_cs`/`freeze_pinned_native` & `is_pinned0` (L1968–2073); JEP 491 vthread unmount & `_vthread_list_head` competitive handoff (L118–160) | source |
| `openjdk/jdk` `186489b55b5df61e270174a76104a2af27cc7197` | `src/java.base/share/classes/jdk/internal/foreign/{MemorySessionImpl,ConfinedSession,SharedSession}.java` | `@Stable int state` & `checkValidStateRaw()` (L66–206); `ConfinedSession.justClose` (L74–83); `SharedSession.justClose` (L83–93) | source |
| `openjdk/jdk` `186489b55b5df61e270174a76104a2af27cc7197` | `src/hotspot/share/prims/scopedMemoryAccess.cpp` | `for_scoped_methods`, `is_accessing_session`, `ScopedAsyncExceptionHandshakeClosure`, `CloseScopedMemoryHandshakeClosure`, `Deoptimization::deoptimize`, `ScopedMemoryAccess_closeScope` (L42–317) | source |
| `openjdk/valhalla` `12e87d09246d366cc74cb409e4c914351256e98b` | `src/hotspot/share/oops/layoutKind.hpp`, `classfile/fieldLayoutBuilder.cpp` | `enum class LayoutKind` (L32–96); layout selection & `can_use_atomic_flat` guard (L45–120) | source |
| `openjdk/valhalla` `12e87d09246d366cc74cb409e4c914351256e98b` | `src/java.base/share/classes/jdk/internal/vm/annotation/{LooselyConsistentValue,NullRestricted}.java` | Tearing and strict-init contracts (L30–51, L30–49) | documentation + source |

### Peer-Reviewed Literature and Specifications

- **Manson, Pugh, Adve (POPL 2005)**: *The Java Memory Model*, DOI `10.1145/1040305.1040336` (normative foundation for JLS §17.4).
- **Ševčík & Aspinall (ECOOP 2008)**: *On Validity of Program Transformations in the Java Memory Model*, DOI `10.1007/978-3-540-70592-5_3` (compiler optimization counterexamples against JMM causality).
- **Batty, Memarian, Nienhuis, Pichon-Pharabod, Sewell (ESOP 2015)**: *The Problem of Programming Language Concurrency Semantics*, DOI `10.1007/978-3-662-46669-8_12` (thin-air impossibility for per-execution axiomatic models).
- **Kang, Hur, Lahav, Vafeiadis, Dreyer (POPL 2017)**: *A Promising Semantics for Relaxed-Memory Concurrency*, DOI `10.1145/3009837.3009850` (certification-based promising operational semantics).
- **OpenJDK JEPs**: JEP 193 (Variable Handles, JDK 9), JEP 401 (Value Classes and Objects, preview), JEP 444 (Virtual Threads, JDK 21), JEP 454 (Foreign Function & Memory API, JDK 22), JEP 491 (Synchronize Virtual Threads without Pinning, JDK 24).

### Reproducible Execution Witnesses (OpenJDK 27.0.1, Linux x86_64, Observed 2026-11-19)

1. **Interface Verifier Deferral (`InterfaceVerifierQuirk.class`, major v65 + `VerifyInterfaceDriver.java`)**:
   - Command: `java -Xverify:all -cp /tmp/jvm_ref_probe VerifyInterfaceDriver`
   - Observed output:
     ```text
     FORGED_RUNNABLE_ACTUAL_CLASS: java.lang.String
     FORGED_INSTANCEOF_RUNNABLE: false
     FORGED_RUN_ICCE: java.lang.IncompatibleClassChangeError: Class java.lang.String does not implement the requested interface java.lang.Runnable
     DIRECT_INVOKEINTERFACE_ICCE: java.lang.IncompatibleClassChangeError: Class java.lang.String does not implement the requested interface java.lang.Runnable
     ```
2. **Bridge Method `checkcast` + `StackMapTable` + Covariant `ArrayStoreException` (`BridgeAndCovariantArray.java`)**:
   - Command: `javac BridgeAndCovariantArray.java && javap -v -p 'BridgeAndCovariantArray$StringBox.class' && java BridgeAndCovariantArray`
   - Observed output: `void set(java.lang.Object)` emitted with `flags: (0x1040) ACC_BRIDGE, ACC_SYNTHETIC` and `checkcast #13 // class java/lang/String`; `BridgeAndCovariantArray.main` emitted 4 `StackMapTable` entries (`full_frame` / `same`); execution printed:
     ```text
     BRIDGE_EXCEPTION: java.lang.ClassCastException at BridgeAndCovariantArray$StringBox.set(BridgeAndCovariantArray.java:7)
     ARRAY_EXCEPTION: java.lang.ArrayStoreException: java.lang.Integer
     ```
3. **Dynamic Class Redefinition CHA/`evol_method` Deoptimization (`RedefAgent.java` + `RedefDriver.java`)**:
   - Command: `java -javaagent:redef-agent.jar -XX:+PrintCompilation -Xlog:redefine+class+nmethod=debug -cp .:redef_v1 RedefDriver`
   - Observed output:
     ```text
     BEFORE_REDEFINE: 500500
     [debug][redefine,class,nmethod] Found evol dependency of nmethod Target.compute((I)I) compile_id=213 on in nmethod metadata
     [debug][redefine,class,nmethod] Found evol dependency of nmethod RedefDriver.hotCaller((LTarget;I)I) compile_id=216 on in nmethod metadata
     [debug][redefine,class,nmethod] Marked dependent nmethods for deopt
     Target::compute (4 bytes)   made not entrant: marked for deoptimization
     RedefDriver::hotCaller (25 bytes)   made not entrant: marked for deoptimization
     AFTER_REDEFINE: 1499500
     ```
4. **Loom Pinning Evolution (`LoomPinningProbe.java`, JFR `jdk.VirtualThreadPinned`)**:
   - Command: `javac LoomPinningProbe.java && java LoomPinningProbe`
   - Observed output:
     ```text
     PINNED_EVENT_COUNT: 1
     PINNED_EVENT: thread=vt-clinit duration_ms=30.332584 frames=[java.lang.VirtualThread.postPinnedEvent, java.lang.VirtualThread.parkOnCarrierThread, java.lang.VirtualThread.park, java.lang.System$1.parkVirtualThread]
     ```
     (`synchronized` contention and sleep inside `synchronized` emitted 0 pinned events).
5. **Panama FFM `Arena` Temporal & Confinement Safety (`PanamaArenaSafety.java`)**:
   - Command: `javac PanamaArenaSafety.java && java PanamaArenaSafety`
   - Observed output:
     ```text
     CONFINED_OWNER_READ: 0x1122334455667788
     CONFINED_CROSS_THREAD: java.lang.WrongThreadException: Attempted access outside owning thread
     CONFINED_AFTER_CLOSE: java.lang.IllegalStateException: Already closed
     SHARED_READS_BEFORE_CLOSE: 3239
     SHARED_CONCURRENT_CLOSE: java.lang.IllegalStateException: Already closed
     ```
6. **JMM Causality Justification Probe (`jmm_causality_probe.py`)**:
   - Observed output:
     ```text
     TC4 (OOTA r1=r2=42) justifiable values: {'x': {0}, 'y': {0}} => 42 forbidden: True
     TC1 (r1=r2=1 allowed via C1->C2->E3): True [('C1', 'r1=0 (hb init) => r1>=0 holds => commit T1:y=1'), ('C2', 'r2=1 (committed in C1) => commit T2:x=1')]
     TC5 (r1=1,r2=1,r3=0 forbidden): True
     ```

## Revalidation

To cheaply verify whether these findings still hold on a newer JDK or Valhalla release without repeating the full investigation:

1. **Verifier interface loophole**: Re-run the 295-byte `InterfaceVerifierQuirk` classfile probe under `java -Xverify:all` and diff `src/hotspot/share/classfile/verificationType.cpp` around `target_klass->is_interface()`. If HotSpot tightens interface assignability, `VerifyInterfaceDriver` will immediately fail at class-load time with `VerifyError` instead of runtime `IncompatibleClassChangeError`.
2. **CHA / `RedefineClasses` dependency invalidation**: Re-run `RedefDriver` with `-javaagent:redef-agent.jar -Xlog:redefine+class+nmethod=debug` and diff `Dependencies::DepType` (`dependencies.hpp`) plus `VM_RedefineClasses::flush_dependent_code` (`jvmtiRedefineClasses.cpp`).
3. **Valhalla layout & tearing rules**: Diff `src/hotspot/share/oops/layoutKind.hpp` and `src/hotspot/share/classfile/fieldLayoutBuilder.cpp` in `openjdk/jdk` once JEP 401 merges into mainline (and test tearing directly with an early-access Valhalla build using `-XX:+EnableValhalla` / `--enable-preview` on a racy `@LooselyConsistentValue` vs. default `value class`).
4. **Loom carrier pinning**: Re-run `LoomPinningProbe` and inspect `jdk.internal.vm.Continuation.Pinned` plus `continuationFreezeThaw.cpp::is_pinned0`. If future JEPs unpin `<clinit>` or native frames, `PINNED_EVENT_COUNT` will drop to `0`.
5. **Panama FFM handshake protocol**: Re-run `PanamaArenaSafety` and diff `src/hotspot/share/prims/scopedMemoryAccess.cpp` (`CloseScopedMemoryHandshakeClosure::do_thread`) to confirm whether C2 loop strip-mining still triggers `Deoptimization::deoptimize` and whether `SharedSession.justClose()` still relies on `Handshake::execute`.
