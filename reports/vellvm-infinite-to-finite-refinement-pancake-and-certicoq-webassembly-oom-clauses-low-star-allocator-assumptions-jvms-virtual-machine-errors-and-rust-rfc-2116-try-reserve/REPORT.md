# Allocation failure in refinement theorems and language specifications: Vellvm infinite-to-finite refinement, CakeML and Pancake, CertiRocq Wasm and GC, CompCert/Œuf, Pilsner, Low*, and the C, C++, Java, Haskell, Rust and Wasm specifications

## Summary

- **One direction only.** Every mechanized compiler theorem examined that has a finite target memory lets the *target* stop with an out-of-memory (OOM) outcome where the source would have continued. None requires the target to succeed where the source fails. The escape has three encodings:
  - **Coinductive cut.** In Vellvm, `ruttc cutUB cutOOM` lets a finite-side OOM event match any infinite-side computation.
  - **Behaviour-set extension with an I/O prefix.** CakeML's `extend_with_resource_limit` adds `Terminate Resource_limit_hit io` for every prefix of an allowed trace. Pancake inherits it, but its theorem becomes exact when a statically computed stack bound is below the available stack.
  - **Terminal flag disjunction.** CertiRocq Wasm promises "correct value and `out_of_mem = 0`, **or** `out_of_mem = 1`".
- **Exclusion by model.** Other developments make allocation total in the model, so failure cannot be represented. The assumption sits in the model, not in the theorem:
  - CompCert: "allocation never fails: we model an infinite memory". Œuf allocates through CompCert's `EF_malloc`.
  - Pilsner: "stack and heap are unbounded".
  - Low\*: "Assuming an infinite amount of memory"; `mmalloc` returns non-null, and the heap is outside the formal λow\* core.
- **The escape makes the theorems vacuous for degenerate targets.** A target that fails immediately satisfies all three encodings, so non-vacuity needs separate evidence: CakeML's `compile_correct_safe_for_space`, Pancake's static stack bound, or testing. The finite Vellvm model also uses `raise_oom` for integer-pointer overflow and for unsupported operations (signed division, signed modulo, negation).
- **Language specifications.** Every specification examined lets a conforming implementation fail where the idealized semantics would not:
  - C++ requires correct execution only "within its resource limits"; C has translation limits.
  - Java: JVMS §6.3 says a `VirtualMachineError` "may be thrown at any time", and JLS §11.1.3 makes it asynchronous.
  - WebAssembly: `memory.grow` is non-deterministic, and exceeding a runtime limit "may terminate that computation".
  - Haskell: `HeapOverflow` and `StackOverflow` are asynchronous exceptions.
  - Rust: infallible growth diverges through `handle_alloc_error`, which aborts by default under `std`; `try_reserve` returns `Err`.
- **Bounded probes (measured).**
  - JVM: at `-Xmx32m`, `OutOfMemoryError: Java heap space` is catchable after 29 MiB are retained. At `-Xss4m`, stack-overflow depth varied from 97,634 to 211,215 across four runs.
  - Rust: under a 1 MiB capped allocator, `Vec::push` aborts (SIGABRT) while `try_reserve` returns `AllocError`. `-Zoom=panic` is rejected.
  - CakeML v3671: binaries exit with status 1 on heap exhaustion and 2 on stack exhaustion. Two of three deep-recursion programs did not exhaust a 1 MiB stack at n = 10⁷.

## Applicability

**How the subjects relate.** This is a comparison across independent systems, each read at the revision in `REPORT.json`. The one exception is Œuf, which is read together with the CompCert memory model it uses.

**Mechanized developments** (Basis: source):
- Vellvm I2F (`vellvm/vellvm@7f0610c38d829b79bf6e867edf410c9e6f928f98`).
- CakeML `compile_correct` and Pancake `pan_to_target_compile_semantics` (`CakeML/cakeml@2874b664e10939a3ee462215b2e068c89c1f70eb`).
- CertiRocq (`CertiRocq/certirocq@ab66e0164e7ecb63e5af95c90c8e479068bf95c2`). This is the renamed CertiCoq; the GitHub API redirects `CertiCoq/certicoq` here.
- Œuf (`uwplse/oeuf@f3e4d236465ba872d1f1b8229548fa0edf8f7a3f`) with CompCert (`AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`).
- Low\* (`FStarLang/lowstar@b45e92ee4f55472b26456ec0d0dd6bfe952b6e11`). The library has moved out of F\*: the tree of `FStarLang/FStar@fc1776afe592ed8eef352c6610614a70d77b3b66` has no `LowStar.Monotonic.Buffer`.
- KaRaMeL (`FStarLang/karamel@6bd5918c7c518adbb973f75f23cdd0900acb7526`).

Nothing was built. Counts of `Admitted` are `grep` counts in the cited files.

**Papers.** Pilsner is examined only through its paper. Beck et al. 2024, Protzenko et al. 2017 and Marlow et al. 2001 were read in full text.

**Specifications** (Basis: normative):
- JVMS and JLS, Java SE 27 Edition.
- The C11 draft N1570, for the malloc wording, and the C23 draft N3220, for translation limits and the clause number 7.24.3.
- The C++ draft N4950.
- WebAssembly core spec source at `WebAssembly/spec@6fca707686ed4f36a1e30ec2ae7d3dd32b276704`, rendered as "WebAssembly 3.0 (2026-11-20)".

Final ISO texts were not examined.

**Runtimes:**
- Rust: source and the probes' rustc are the same commit, `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (1.102.0-nightly).
- HotSpot: source at `openjdk/jdk27u@d0ae11687ce2623829506888c0305af509d57f4c` (`jdk-27.0.1-ga`). The probes ran on a downstream vendor build reporting 27.0.1; that it matches the tag is assumed.
- GHC: source only (`ghc/ghc@83038fbee5efea8e3ebd5090b2ff5537462e169d`).
- CakeML: release v3671 (commit `16bdb1aaaab64a6ac66504ad2e9f0ed6146060e9`). Its `cml_exit` is byte-identical to the pinned HEAD's.

**Out of scope.** Space-cost semantics (`is_safe_for_space`), stack-bound extensions of CompCert and OS overcommit are mentioned only where they bear on vacuity.

## Findings

### 1. Cross-system table

| System | Source memory | Target memory | Failure representation | Direction permitted | In top-level theorem? | Basis |
|---|---|---|---|---|---|---|
| Vellvm I2F | infinite (`iptr := Z`, `from_Z x := ret x`) | finite `int64`; out-of-range `from_Z`, carry, underflow and overflow raise OOM | `OOME` event; `ruttc` right cut `EqCutR` | target may OOM at any `Vis` point; source UB matches anything (left cut) | yes: `I2F_interpreter_param` | source |
| CakeML | clocked big-step, unbounded | machine code, configured heap and stack | `Terminate Resource_limit_hit io_list` | early stop with any prefix of an allowed trace | yes: `compile_correct` (`machine_sem … ⊆ extend_with_resource_limit behaviours`) | source + execution |
| Pancake | `panSem`, no heap allocation | CakeML backend | `extend_with_resource_limit' (option_lt stack_max (SOME limit))` | early stop only if the static stack bound is absent or not below the available stack | yes: `pan_to_target_compile_semantics` | source |
| CertiRocq → Wasm | λANF big-step, terminating runs only | linear memory, `lim_max` = 30000 pages | global `out_of_mem := 1` when `memory.grow` returns −1 | target may end with `out_of_mem = 1` instead of the value | yes: `LambdaANF_Wasm_related` | source |
| CertiRocq → Clight + GC | λANF | C heap via `gc_stack.c` | `abort_with` → `exit(1)` | unverified runtime path | no: Clight proof not in `theories/_CoqProject` | source |
| Œuf / CompCert | Gallina subset | CompCert memory, total `alloc` | none (`EF_malloc` always succeeds in the model) | not representable | no; model assumption | source |
| Pilsner | ML-like S, finite heap per configuration | idealized T, "stack and heap are unbounded" | none ("finiteness guarantees that allocation will succeed") | not representable | no; model assumption | documentation |
| Low\* / λow\* | F\* `HyperStack` | C via KaRaMeL | `mmalloc` non-null; `mmalloc_partial` may return null in its spec but is implemented as `mmalloc` | not representable for `mmalloc` | no; λow\* "only use[s] stack memory" | source + documentation |

Derived: in every row with a finite target, OOM outcomes are added on the target side only.

### 2. Vellvm: infinite-to-finite refinement (I2F)

`Refinement.v:64-65` defines `PInf := @ParamsV IPZ IPZTheory` and `PFin := @ParamsV IP64Bit IP64BitTheory`. The value relation is `I2F_Iptr z i := z = unsigned i` (`:69-70`).

**Pure computations.** The comment at `:171-180` reads "lockstep on returns and errors, while UB on the infinite (left) side and OOM on the finite (right) side short-circuit":

```coq
Variant I2F_EOU {A1 A2} (RR : A1 -> A2 -> Prop) : EOU A1 -> EOU A2 -> Prop :=
  | I2F_EOU_ret a1 a2 : RR a1 a2 -> I2F_EOU RR (raise_ret a1) (raise_ret a2)
  | I2F_EOU_error s1 s2 : I2F_EOU RR (raise_error s1) (raise_error s2)
  | I2F_EOU_ub s m : I2F_EOU RR (raise_ub s) m
  | I2F_EOU_oom m s : I2F_EOU RR m (raise_oom s)
```

**Effectful computations.** The relation is `I2F_refine_MCFG RR := ruttc cutUB cutOOM I2FE_MCFG I2FA_MCFG RR` (`:447-461`). Its comment says "short-circuited if the finite side runs out of memory (cut on OOM on the right); UB should arise simultaneously on both sides, so we may cut it off on the left". `ruttc` is a paco greatest fixed point (`rutt_cutoff.v:164`), and its two new constructors are (`:146-151`):

```coq
| EqCutL : forall (A : Type) (e : E1 A) k t, Rcutl e -> ruttcF sim (VisF e k) t
| EqCutR : forall (B : Type) (e : E2 B) k t, Rcutr e -> ruttcF sim t (VisF e k).
```

A finite-side OOM is therefore accepted only where it occurs, after lockstep agreement. The paper says the same: OOM "refines any behavior (but not in a 'time-traveling' fashion—the programs must agree up until the O∅ occurs)", and it is "a kind of refinement dual to UB" (Beck et al. 2024, §4).

**Top-level theorem.** `I2F_toplevel.v:458-466`:

```coq
Theorem I2F_interpreter_param :
  forall (args : list string) (prog : ll_toplevel_entities),
    I2F_refine_MCFGbot (prod_rel I2F_FusedS I2F_dvalue)
      (@interpreter_param PInf args prog) (@interpreter_param PFin args prog).
```

It relates *one* program under two memory models. It is the lowering phase of the two-phase design: optimize on VIR_inf, lower once to VIR_fin, and only remove the inserted bounds checks on finite programs (Beck et al. §3.5, §6). The eight `Theory/I2F` files and `rutt_cutoff.v` contain no `Admitted`. Basis: source + documentation.

**Where the finite model raises OOM.** `IPtrFinite.v` has 8 `raise_oom` sites:

| Operation | Lines | Raises OOM when |
|---|---|---|
| `from_Z_bits` | `:12-16` | x > max_unsigned or x < 0 |
| `madd` | `:32-35` | carry |
| `msub` | `:39-42` | unsigned underflow |
| `mmul` | `:46-51` | overflow |
| `mshl` | `:59-64` | overflow |
| `mdivs` | `:54` | always |
| `mmods` | `:57` | always |
| `mnegative` | `:68` | always |

OOM is thus also the finite model's catch-all for integer-pointer behaviour it does not represent. The paper anticipates overflow: "should this overflow in the finite model the allowed behavior will only be OOM". Basis: source + documentation.

**Latent inconsistency (not a bug at this revision).** The instance `VMemInt_intptr_ix {sz}` is generic, but `mmul` hard-codes 64 (`IPtrFinite.v:46-51`):

```coq
mmul :=
  fun x y =>
    let res := ((Integers.unsigned x) * (Integers.unsigned y))%Z in
    if (res >? @Integers.max_unsigned 64)
    then raise_oom "IPBit multiplication overflow."
    else ret (@Integers.repr sz res);
```

The only instantiation is `@VMemInt_intptr_ix 64` (`:99`), so the check is exact here. An instantiation with `sz < 64` would wrap silently rather than raise OOM. Basis: source + derived.

**Dead allocations.** In a finite model, "allocations, even dead ones, cannot be removed" (Beck et al. §2). The two-phase design moves such optimizations to the infinite phase. Basis: documentation.

### 3. CakeML and Pancake

**Outcomes and behaviours** (`semantics/ffi/ffiScript.sml`):
- `outcome = Success | Resource_limit_hit | FFI_outcome final_event` (`:83`).
- `behaviour = Diverge (io_event llist) | Terminate outcome (io_event list) | Fail` (`:90-101`).

**The extension** (`semantics/proofs/semanticsPropsScript.sml:219-226`):

```sml
extend_with_resource_limit behaviours =
  behaviours ∪
  { Terminate Resource_limit_hit io_list | io_list | ∃t l. Terminate t l ∈ behaviours ∧ io_list ≼ l } ∪
  { Terminate Resource_limit_hit io_list | io_list | ∃ll. Diverge ll ∈ behaviours ∧ LPREFIX (fromList io_list) ll }
```

The primed variant is `extend_with_resource_limit' precise b = if precise then b else extend_with_resource_limit b` (`:228-232`).

**The top-level theorem.** `compile_correct` (`compiler/proofs/compilerProofScript.sml:312-328`) states, for `M_success (code,data,c)`, that `semantics_init … = Execute behaviours` and `machine_sem mc ffi ms ⊆ extend_with_resource_limit behaviours` for every installed state.
- `ParseError` and `TypeError` map to `CannotParse` and `IllTyped`.
- `AssembleError` and `ConfigError` give `T`.
- `compile_correct_safe_for_space` (`:289-310`) removes the extension under `∀po. is_safe_for_space … (read_limits cc mc ms)`.

**How the target signals the outcome.** At the halt address, a zero pointer register means `Halt Success`; anything else means `Halt Resource_limit_hit` (`compiler/backend/semantics/targetSemScript.sml:138-140`). In the release, `cake_exit: callq cdecl(cml_exit)` passes that register.

The runtime side is `basis/basis_ffi.c`:
- `cml_exit` prints "Program exited with nonzero exit code." under the default `STDERR_MEM_EXHAUST` (`:55-59`, `:746-768`).
- Under `DEBUG_FFI` it labels status 1 "CakeML heap space exhausted." and status 2 "CakeML stack space exhausted.".
- `CML_HEAP_SIZE` and `CML_STACK_SIZE` are in MiB and default to 1024 each (`:861-874`). Both come from one `malloc(heap_size + stack_size)` (`:876-906`).

Basis: source.

**Measured on the v3671 release** (x86_64 Linux; build commands in `support/README.txt`):

| Program | Limits (MiB) | n | Result |
|---|---|---|---|
| tail-recursive list build (`cakeml_heap.cml`) | heap 16 | 10³ | prints 1000, status 0 |
| same | heap 16 | 10⁷ | status 1, peak RSS 18,396 KB |
| same | heap 1024 | 10⁷ | prints 10000000, status 0, peak RSS 240,776 KB |
| `1 + deep (n-1)` (`cakeml_stack.cml`) | stack 1 | 10⁷ | status 0 |
| `n :: mk (n-1)` (`cakeml_stack2.cml`) | stack 1, heap 1024 | 10⁷ | status 0 |
| `let r = deep (n-1) in if r < 0 …` (`cakeml_stack3.cml`) | stack 1 | 10⁷ | status 2 |
| same | stack 1024 | 10⁷ | status 0 |

Under different configured limits, the same binary either terminates normally or stops early, which is exactly the latitude of `extend_with_resource_limit`. A 1 MiB stack holds about 43,690 frames of 24 bytes (derived: 1,048,576 / 24). The two programs that survived at depth 10⁷ were therefore presumably compiled to tail calls; which pass did so was not established. Whether a source program hits the limit is a property of the compiled code. Basis: execution (`support/outputs/cakeml_run*.log`) + derived.

**Pancake.** `pan_to_target_compile_semantics` (`pancake/proofs/pan_to_targetProofScript.sml:1285-1326`) assumes `compile_prog_max c mc pan_code = (SOME (bytes, nbitmaps, c'), stack_max)` plus installation and layout conditions. It concludes:

```sml
machine_sem mc ffi ms ⊆
  extend_with_resource_limit'
    (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
    {semantics_decls s start pan_code}
```

Here `option_lt (SOME n1) (SOME n2) ⇔ n1 < n2` and `option_lt NONE (SOME _) ⇔ F` (`:1185-1188`). `stack_max` is `max_depth c'.stack_frame_size (full_call_graph …)` (`:1174-1183`). When the call-graph bound exists and is strictly below the stack limit, the theorem is exact.

Heap exhaustion is excluded by construction: `panLang_wordSem_neq_NotEnoughSpace` proves `res ≠ SOME NotEnoughSpace` using `no_alloc` (`:1026-1052`). Neither theorem file contains `cheat`. Basis: source.

### 4. CertiRocq: Wasm backend, Clight backend and GC

**Code generation.** `grow_memory_if_necessary` (`theories/CodegenWasm/LambdaANF_to_Wasm.v:274-296`) grows memory by one page when needed. On `BI_memory_grow (* returns -1 on alloc failure *)` it runs `[ BI_const_num (nat_to_value 1); BI_global_set glob_out_of_mem; BI_return ] (* out of memory, abort *)`.
- The limit is `Definition max_mem_pages := 30000%N.` (`:28`), used at `lim_max := Some max_mem_pages (* to ensure, i32 ptr doesn't overflow, but memory grow fails instead *)` (`:594`).
- Derived: 30000 × 65,536 = 1,966,080,000 bytes.
- After each `call_indirect`, call sites test the flag and return (`LambdaANF_to_Wasm_correct.v:410-432`).

**What the theorem promises.** The result relation (`LambdaANF_to_Wasm_correct.v:973-980`) is:

```coq
Definition result_val_LambdaANF_Wasm val sr inst : Prop :=
     (exists res_i32 wasmval, sglob_val sr inst glob_result = Some (VAL_num (VAL_int32 res_i32))
         /\ wasm_value_to_i32 wasmval = res_i32 /\ repr_val_LambdaANF_Wasm val sr inst wasmval
         /\ (sglob_val sr inst glob_out_of_mem = Some (VAL_num (nat_to_value 0))))
  \/ (sglob_val sr inst glob_out_of_mem = Some (VAL_num (nat_to_value 1))).
```

`LambdaANF_Wasm_related` (`theories/CodegenWasm/toplevel_theorem.v:37-69`) assumes `bstep_e pfs cenv (M.empty _) e v n` and successful compilation. It concludes that instantiation succeeds and that `main` reaches a store satisfying the relation. It therefore covers terminating source runs only, and the OOM disjunct is available at every growth. Neither file contains `Admitted`.

This matches the normative Wasm rule: `memory.grow` "may either succeed … or fail, returning −1. Failure *must* occur if … a maximum size … would be exceeded. However, failure *can* occur in other cases as well" (`document/core/exec/instructions.rst:640-645`). Basis: source + normative.

**End-to-end status at this revision.**
- `theories/Compiler/correctness.v:218-261` (`metarocq_anf_pipeline`) ends in `Admitted.` with three `admit`s.
- `theories/Codegen/LambdaANF_to_Clight_correct.v` has 10,766 lines and 6 textual `Admitted` (at least one inside a comment). It is not listed in `theories/_CoqProject`, which lists `CodegenWasm/LambdaANF_to_Wasm_correct.v` (line 98) and `Compiler/correctness.v` (line 112).

So the default build does not check the Clight proof. Basis: source.

**GC failure.** In `runtime/gc_stack.c`, every failure exits through `abort_with(char *s) { fprintf(stderr, "%s", s); exit(1); }` (`:153-156`). The messages are:
- "Could not create the next generation" when `malloc` fails in `create_space` (`:324-341`).
- "Nursery is too small for function's num_allocs" (`:377-393`).
- "Ran out of generations" (`:433-435`).

`gc_stack.h:113-115` sets `LOG_NURSERY_SIZE 16` and `MAX_SPACES (8*sizeof(value)-(2+LOG_WORDSIZE+LOG_NURSERY_SIZE))`, which is 43 doubling generations on 64-bit (derived: 64 − 21). No heap ceiling is configurable; only `malloc` failure surfaces exhaustion. The interface comment (`gc_stack.h:141-151`) specifies only the success case. Basis: source + derived.

### 5. Exclusion by model: CompCert/Œuf, Pilsner, Low\*

- **CompCert.** `common/Memory.v:345-348` says "Note that allocation never fails: we model an infinite memory." `extcall_malloc_sem` (`common/Events.v:964-969`) has one constructor, built on that total `Mem.alloc`. Œuf's `step_alloc` (`src/Dmajor.v:219-224`) requires `external_call EF_malloc ge (v :: nil) m t vres m'`. A real NULL return therefore has no counterpart in the proof. Basis: source.
- **Pilsner** (Neis et al. 2015, §4–5). The paper says: "machine words are unbounded natural numbers and stack and heap are unbounded as well". A configuration must carry "a valid and finite heap (finiteness guarantees that allocation will succeed)", and registered values "stay allocated forever". Basis: documentation.
- **Low\*** (Protzenko et al. 2017, §2–3). The paper says: "Assuming an infinite amount of memory, alloc's pre-condition is trivial"; "memory allocation … may cause a (fatal) error as it runs out of memory". λow\* uses only stack memory, "leaving the heap out of λow\*", and the transcription "is not backed by a specific proof". Basis: documentation.

  In the library (`lib/LowStar.Monotonic.Buffer.fsti`):
  - `malloc_pre r len = HST.is_eternal_region r /\ U32.v len > 0` (`:2061`).
  - `mmalloc` returns an `lmbuffer`, whose refinement includes `not (g_is_null b)` (`:2037-2038`, `:2116-2120`).
  - `mmalloc_partial` admits null in its spec, but its body is `= mmalloc r init len` (`:2141-2146`). The design note explains why that is allowed: "their spec should be valid even when their implementation just returns null" (`:2030-2035`).

  KaRaMeL:
  - `KRML_HOST_MALLOC` is plain `malloc` (`include/krml/internal/target.h:62-64`).
  - `KRML_CHECK_SIZE` exits with status 253 on element-count overflow (`:216-226`).

  Basis: source.

### 6. Language specifications

| Specification | Where failure surfaces | May a conforming implementation fail where the idealized semantics would not? | Recoverable? | Basis |
|---|---|---|---|---|
| C (N1570 §7.22.3; C23 §7.24.3) | at the call: "If the space cannot be allocated, a null pointer is returned." Stack exhaustion is unspecified. | yes: N3220 §5.2.5.2 requires the implementation to "translate and execute a program that uses but does not exceed the following limitations" | `malloc`: yes | normative |
| C++ (N4950 [intro.compliance.general]/2.1; [basic.stc.dynamic.allocation]/4; [implimits]) | throwing forms "only by throwing … `std::bad_alloc`"; non-throwing forms return null; a new-handler may run | yes: correct execution is required only "within its resource limits"; the [implimits] quantities "do not determine compliance" | yes | normative |
| JVMS SE 27 §6.3 | "cannot predict where … resource limitations may be encountered … may be thrown at any time" | yes | catchable (probes) | normative |
| JLS SE 27 §11.1.3 | `StackOverflowError` is thrown synchronously at invocation "as well as asynchronously"; `OutOfMemoryError` at creation, class initialization or boxing "as well as asynchronously"; "a small but bounded amount of execution" may precede it | yes | yes | normative |
| Wasm (instructions.rst:640-645; implementation.rst:127-157) | `memory.grow` → −1 non-deterministically; exceeding frame, value or memory limits "may terminate that computation and report an implementation-specific error" | yes | `memory.grow`: yes; runtime limits: no | normative |
| Haskell / GHC (Marlow et al. 2001; `GHC.Internal.IO.Exception:206-228`) | asynchronous `StackOverflow` and `HeapOverflow`: "Since such exceptions can occur at almost any program point, it is natural to treat them as asynchronous." | yes | only for an explicit RTS limit; OS allocation failure "results in immediate termination" | documentation + source |
| Rust (RFC 2116; `alloc`/`std` at 3ef0c22c) | infallible APIs → `handle_alloc_error`; `try_reserve{,_exact}` → `Result<(), TryReserveError>` | yes | infallible: no by default (abort); fallible: yes | documentation + source + execution |

**GHC RTS** (83038fbe):
- GC sets `heap_overflow` (`rts/sm/GC.c:1175-1177`).
- The scheduler then throws `heapOverflow_closure` to the main thread, after a grace window `heapLimitGrace` that defaults to 1 MiB. If there is no main thread, it shuts down (`rts/Schedule.c:1979-2017`; `rts/RtsFlags.c:162`).
- `-M` is off by default (`:161`).
- The default `-K` is 80% of physical memory (`:140-151`). `threadStackOverflow` throws `stackOverflow_closure` (`rts/Threads.c:587-622`).
- The scheduler calls the mechanism "neither reliable … nor very usable".

**HotSpot** (`jdk-27.0.1-ga`):
- Heap allocation failure throws the preallocated "Java heap space" error (`gc/shared/memAllocator.cpp:112-138`).
- The other preallocated messages include "Requested array size exceeds VM limit" (`memory/universe.cpp:797-815`).
- Direct buffers throw "Cannot reserve N bytes of direct buffer memory" after a sleep-and-retry loop (`java/nio/Bits.java:176-189`).

Basis: source.

### 7. Rust: RFC 2116 against the library at the probe's commit

RFC 2116 explains the original policy: "Early on in Rust's history we made a policy decision not to expose this fact at the API level, preferring to abort". It proposed two mechanisms: `oom=panic` (a `-C oom=abort|panic` flag) and `try_reserve`/`try_reserve_exact` returning `Result<(), CollectionAllocErr>`.

At `3ef0c22c`:
- **Error type.** `TryReserveError { kind: TryReserveErrorKind }` is stable since 1.57.0 (`library/alloc/src/collections/mod.rs:67-73`). Its kinds are `CapacityOverflow` ("usually `isize::MAX` bytes") and `AllocError { layout, .. }`; the `kind()` accessor is unstable (`:79-121`).
- **Infallible path.** `handle_alloc_error` "is guaranteed to diverge". With `std` linked, it "print[s] a message to standard error and abort[s] the process" (`library/alloc/src/alloc.rs:639-689`).
- **The hook.** `std`'s `rust_oom` runs the alloc-error hook and then calls `crate::process::abort()` (`library/std/src/alloc.rs:443-450`). Only a panicking hook, installed with the unstable `set_alloc_error_hook`, makes OOM unwind.
- **`oom=panic` did not ship.** `rustc -Zoom=panic` fails: "error: unknown unstable option: `oom`".

Basis: documentation + source + execution.

### 8. Probe results (execution)

All runs were on x86_64 Linux 7.1 (Xeon @ 2.60 GHz), each under `timeout 60` and `taskset -c 0-7`, one at a time. Toolchains are listed in `support/README.txt`.

| Probe | Limit | Observed | Continued? | Peak RSS |
|---|---|---|---|---|
| JVM: retain 1 MiB arrays | `-Xmx32m` | `OutOfMemoryError: Java heap space` after 29 MiB (`maxMemory` 33,488,896) | yes (42 ms) | 70,192 KB |
| same | `-Xmx64m` | same, after 59 MiB | yes | 105,756 KB |
| JVM: `new long[Integer.MAX_VALUE]` | `-Xmx64m` | "Requested array size exceeds VM limit" | yes | 44,480 KB |
| JVM recursion | `-Xss256k` | `StackOverflowError` at depths 1,844 / 1,844 / 1,844 / 1,898 | yes | 43,444 KB |
| same | `-Xss1m` | depths 18,936 / 21,025 / 19,435 / 20,935 | yes | 44,436 KB |
| same | `-Xss4m` | depths 194,511 / 97,634 / 211,215 / 98,330 | yes | 62,048 KB |
| JVM direct buffers | `-XX:MaxDirectMemorySize=8m` | "Cannot reserve 1048576 bytes of direct buffer memory (allocated: 8388608, limit: 8388608)" | yes (545 ms) | 52,296 KB |
| Rust `Vec<u64>::push` loop | 1 MiB capped allocator | "memory allocation of 1048576 bytes failed", SIGABRT (status 134) | no | 2,372 KB |
| Rust `try_reserve` doubling | same | `Err(AllocError { layout: size 1048576, align 8 })` with 524,288 bytes of vector data | yes | 2,352 KB |
| Rust `try_reserve(usize::MAX)` | same | `CapacityOverflow`, allocator not called | yes | 1,600 KB |
| Rust push, panicking hook inside `catch_unwind` | same | panic caught, `catch_unwind` returns `Err` | yes | 2,368 KB |
| Rust `vec![0u8; 2 MiB]` | same | "memory allocation of 2097152 bytes failed", SIGABRT | no | 1,548 KB |
| C `malloc(16 MiB)` loop | `RLIMIT_AS` 256 MiB | NULL after 15 calls | yes | 248,720 KB |
| C++ `new char[16 MiB]` | same | `std::bad_alloc` after 15 | yes | 249,060 KB |
| C++ `new (std::nothrow)` | same | `nullptr` after 15 | yes | 248,744 KB |

**Stack-overflow depth is not determined by the program and limit alone.** Under `-Xss4m`, the depth varied by up to 2.16× (derived: 211,215 / 97,634). That interpreted and JIT-compiled frames differ in size is a hypothesis.

**The Rust cap counts old and new storage during growth.** The capped allocator keeps the default `GlobalAlloc::realloc`, which allocates, copies, then frees. Growing 512 KiB → 1 MiB therefore needed 1.5 MiB live. The size at which growth fails depends on the `realloc` strategy, not only on the cap (derived).

Raw output: `support/outputs/run.log`, `stack_repeats.log`.

### 9. Performance and resource footprint (L1–L6)

| Level | Quantity | Value | Basis |
|---|---|---|---|
| L1 | Vellvm `Theory/I2F` (8 files) vs the two `iptr` instances | 7,652 vs 174 lines (≈ 44:1; crude, since I2F re-proves whole-semantics congruence) | execution (`wc -l`) + derived |
| L1 | CertiRocq Wasm correctness vs generator | 6,050 vs 631 lines (≈ 9.6:1) | execution + derived |
| L1 | Pancake end-to-end proof file | 2,572 lines | execution |
| L1 | person-months, token budgets | not measured | — |
| L2 | CakeML compiler binary from release assembly | 2.12 s, 105,936 KB peak RSS | execution |
| L2 | building any proof development | not measured | — |
| L3 | CakeML v3671 compiling a 3-line program plus basis | 0.52–0.55 s, ≈ 750 MB peak RSS | execution |
| L4 | Vellvm finite bounds checks | not measured. Beck et al. only "believe" they are not "a significant impediment" | documentation |
| L4 | CertiRocq per-allocation and per-call OOM checks | not measured | — |
| L4 | time to report exhaustion: JVM heap / CakeML heap / Rust | 42 ms / 0.01 s / 0.11 s (Rust includes abort) | execution |
| L5 | proof replay time | not measured | — |
| L6 | CertiRocq Wasm memory ceiling | 1,966,080,000 bytes | source + derived |
| L6 | CakeML default reservation | 2 GiB (1024 + 1024 MiB, one `malloc`) | source |
| L6 | GHC defaults | `-M` unlimited; `-K` 80% of RAM; grace 1 MiB | source |

### 10. Comprehensibility and simplicity (C1, C2)

**C1 (derived).** To read these theorems correctly, a reader must recover three things:
- (a) the encoding of the escape: cut, set extension or flag;
- (b) whether the escape respects the observed I/O prefix;
- (c) what non-vacuity evidence exists.

The systems differ in how visible these are:
- **CakeML.** The prefix condition is visible in one definition (`≼`, `LPREFIX`).
- **Vellvm.** It is implicit in the coinductive structure of `ruttc`.
- **CertiRocq Wasm.** The relation is about the final store only; λANF has no I/O. Reading "or `out_of_mem = 1`" as "fails only when memory is really exhausted" would be wrong.
- **Model-level exclusion** is the hardest to audit: the theorem never mentions memory. In Vellvm's finite model, an OOM diagnostic may not concern memory at all (`mdivs`, `mmods`, `mnegative`).

**C2 (derived; a hypothesis beyond the systems examined).** The three positive encodings are instances of one relation:

T ⊆ S ∪ { p·⊥_res : p a finite observable prefix of some s ∈ S }

CakeML spells it out over I/O lists, Vellvm realizes it coinductively over events, and CertiRocq Wasm instantiates it with an empty observable (p = ε). Pancake's `option_lt` switch and CakeML's safe-for-space theorem turn the escape off under a predicate on the target configuration. "Exact" and "escape" are thus one parameter, not two theorem shapes.

The language specifications place the same escape at different granularities:
- C and C++: synchronous, at one call, so the prefix is exact.
- Java and Haskell: asynchronous. The JLS also allows "a small but bounded amount of execution" before delivery, which is weaker than prefix-exactness.
- Wasm: both (−1 from `memory.grow`, plus termination when a runtime limit is exceeded).

### 11. Validation of the statements themselves (V1–V4)

- **V1 (specification adequacy).** Each escape relation admits a target that fails immediately:
  - `Terminate Resource_limit_hit []` is in `extend_with_resource_limit S` whenever S contains a terminating or diverging behaviour;
  - a first-event `ThrowOOM` satisfies `ruttc … cutOOM`;
  - `out_of_mem = 1` satisfies `result_val_LambdaANF_Wasm`.

  Non-vacuity evidence found: `compile_correct_safe_for_space` and Pancake's exact case (source), and the runs in §3 and §8 (execution). Beck et al. say plainly: "we purposefully do not want to reason about programs that run out of memory." Spec-mutation testing was not examined.
- **V2 (compiler fuzzing).** Differential testing under memory limits was not examined.
- **V3 (concurrency and timing).** JVM overflow depth is non-deterministic (measured). GHC: "It is undefined which thread receives this exception" (source). Schedule exploration was not examined.
- **V4 (programmer models).** Whether programmers read `try_reserve` or `extend_with_resource_limit` correctly was not examined.

## Boundaries

- **Not examined:**
  - The papers by Zakowski et al. 2021, Tan et al. 2019, Pohjola et al. 2023, Paraskevopoulou–Li–Appel 2021, Meier et al. 2025 and Mullen et al. 2018 were not read; their metadata was checked on Crossref. All claims about those systems rest on the pinned source.
  - No Pilsner artifact.
  - Final ISO C and C++ texts.
  - The space-cost semantics behind `is_safe_for_space`.
  - Stack exhaustion in CompCert-compiled Œuf or Low\* code.
  - The individual admitted lemmas of the CertiRocq Clight proof.
  - The original `womeier/certicoqwasm` artifact.
  - Which CakeML pass removed the stack growth in `cakeml_stack.cml` and `cakeml_stack2.cml`, and whether that pass is verified.
- **Unknown:**
  - Whether the vendor JVM binary corresponds exactly to `jdk-27.0.1-ga`.
  - The cause of the JVM depth variance.
  - Whether `LambdaANF_to_Wasm_correct.v` depends on admitted lemmas in other files.
  - Whether Vellvm's I2F builds at the pin (it was not built).
- **Known not to apply:**
  - The I2F theorem is not a compiler-correctness theorem.
  - CertiRocq's Wasm theorem says nothing about diverging sources.
  - Pancake's freedom from heap exhaustion does not carry over to CakeML.
- **Unsupported:**
  - `-Zoom=panic` in rustc 1.102.0-nightly.
  - A heap-limit option in the CertiRocq GC.
  - The GHC heap-limit probe (`+RTS -M`) was not run because no GHC was available on the probe host. GHC behaviour here is from source.
- **Stronger conclusions not established:**
  - That any examined compiler avoids unnecessary OOM (the theorems permit it).
  - That the one-direction pattern holds for compilers not examined.
  - That Vellvm's bounds checks are cheap.
  - That catching `OutOfMemoryError` is safe beyond these single-threaded probes.

## Evidence

All evidence was observed on 2026-11-21.

**Vellvm** (`vellvm/vellvm@7f0610c38d829b79bf6e867edf410c9e6f928f98`):
- `src/rocq/Theory/I2F/Refinement.v:64-70,171-180,298-299,373-374,447-472`
- `src/rocq/Utils/rutt_cutoff.v:128-164`
- `src/rocq/Semantics/Implementations/IPtrFinite.v:12-107`
- `src/rocq/Semantics/Implementations/IPtrInfinite.v:10-26`
- `src/rocq/Theory/I2F/I2F_toplevel.v:458-466`

**CakeML** (`CakeML/cakeml@2874b664e10939a3ee462215b2e068c89c1f70eb`):
- `compiler/proofs/compilerProofScript.sml:289-328`
- `semantics/proofs/semanticsPropsScript.sml:219-240`
- `semantics/ffi/ffiScript.sml:83-101`
- `compiler/backend/semantics/targetSemScript.sml:138-140`
- `pancake/proofs/pan_to_targetProofScript.sml:1026-1052,1174-1188,1285-1326`
- `basis/basis_ffi.c:55-82,746-768,861-906`

**CakeML release** v3671: `cake-x64-64.tar.gz`, sha256 `e3edd113497bf7fce443e69c70f09c3df1942849251c86ce8e44e6327ade0d3d`, from `CakeML/cakeml@16bdb1aaaab64a6ac66504ad2e9f0ed6146060e9`.

**CertiRocq** (`CertiRocq/certirocq@ab66e0164e7ecb63e5af95c90c8e479068bf95c2`):
- `theories/CodegenWasm/LambdaANF_to_Wasm.v:27-28,274-296,594`
- `theories/CodegenWasm/LambdaANF_to_Wasm_correct.v:410-432,973-980,1055-1057`
- `theories/CodegenWasm/toplevel_theorem.v:37-69`
- `theories/Compiler/correctness.v:218-261`
- `theories/_CoqProject:98,112`
- `runtime/gc_stack.c:78-92,153-156,324-341,377-436`
- `runtime/gc_stack.h:113-151`

**Œuf** (`uwplse/oeuf@f3e4d236465ba872d1f1b8229548fa0edf8f7a3f`): `src/Dmajor.v:219-224`.

**CompCert** (`AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`): `common/Memory.v:345-357`; `common/Events.v:964-969`.

**Low\*** (`FStarLang/lowstar@b45e92ee4f55472b26456ec0d0dd6bfe952b6e11`): `lib/LowStar.Monotonic.Buffer.fsti:2008-2061,2116-2146`.

**KaRaMeL** (`FStarLang/karamel@6bd5918c7c518adbb973f75f23cdd0900acb7526`): `include/krml/internal/target.h:58-72,199-226`.

**Rust RFC 2116** (`rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`): `text/2116-alloc-me-maybe.md`.

**Rust** (`rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`):
- `library/alloc/src/alloc.rs:628-703`
- `library/alloc/src/collections/mod.rs:67-121`
- `library/std/src/alloc.rs:375-450`

**GHC** (`ghc/ghc@83038fbee5efea8e3ebd5090b2ff5537462e169d`):
- `rts/Schedule.c:75-84,1979-2017`
- `rts/sm/GC.c:1175-1177`
- `rts/Threads.c:575-622`
- `rts/RtsFlags.c:140-162`
- `libraries/ghc-internal/src/GHC/Internal/IO/Exception.hs:206-228`

**OpenJDK** (`openjdk/jdk27u@d0ae11687ce2623829506888c0305af509d57f4c`):
- `src/hotspot/share/gc/shared/memAllocator.cpp:112-138`
- `src/hotspot/share/memory/universe.cpp:797-815`
- `src/java.base/share/classes/java/nio/Bits.java:176-189`

**WebAssembly** (`WebAssembly/spec@6fca707686ed4f36a1e30ec2ae7d3dd32b276704`): `document/core/exec/instructions.rst:640-645`; `document/core/appendix/implementation.rst:125-157`.

**Specifications:**
- JVMS SE 27 §6.3: https://docs.oracle.com/javase/specs/jvms/se27/html/jvms-6.html
- JLS SE 27 §11.1.3: https://docs.oracle.com/javase/specs/jls/se27/html/jls-11.html
- C11 N1570 §7.22.3: https://port70.net/~nsz/c/c11/n1570.html
- C23 N3220 §5.2.5.2 and the table of contents for §7.24.3: https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3220.pdf
- C++ N4950: https://timsong-cpp.github.io/cppwp/n4950/

**Papers read** (metadata checked through the Crossref REST API on 2026-11-21):
- Beck, Yoon, Chen, Zakowski, Zdancewic, PACMPL 8(ICFP) 2024, doi:10.1145/3674652, arXiv:2404.16143.
- Neis, Hur, Kaiser, McLaughlin, Dreyer, Vafeiadis, ICFP 2015, doi:10.1145/2784731.2784764.
- Protzenko et al., PACMPL 1(ICFP) 2017, doi:10.1145/3110261, arXiv:1703.00053.
- Marlow, Peyton Jones, Moran, Reppy, PLDI 2001, doi:10.1145/378795.378858.

**Bibliographic context only** (Crossref metadata checked; content not examined):
- doi:10.1145/3473572 (Zakowski et al. 2021)
- doi:10.1017/S0956796818000229 (Tan et al. 2019)
- doi:10.1145/3623759.3624544 (Åman Pohjola et al. 2023)
- doi:10.1145/3473591 (Paraskevopoulou, Li, Appel 2021)
- doi:10.1145/3703595.3705879 (Meier et al. 2025)
- doi:10.1145/3167089 (Mullen et al. 2018)

**Execution.** Probe sources, scripts, logs and exit-status conventions are in `support/` (see `support/README.txt`). Host: x86_64 Linux 7.1 on an Intel Xeon @ 2.60 GHz. Toolchains: OpenJDK 27.0.1 (vendor build); rustc 1.102.0-nightly (3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1); gcc/g++ 15.2.0; glibc 2.43; CakeML v3671.

## Revalidation

- **Vellvm.** At a new revision, check that `I2F_refine_MCFG` in `Theory/I2F/Refinement.v` is still `ruttc cutUB cutOOM …` and that `I2F_interpreter_param` exists. Count `raise_oom` in `IPtrFinite.v` (8 at 7f0610c3).
- **CakeML and Pancake.** Grep `extend_with_resource_limit` in the conclusions of `compile_correct` and `pan_to_target_compile_semantics`. If either became exact, the direction claim would change.
- **CertiRocq.** Grep `glob_out_of_mem = Some (VAL_num (nat_to_value 1))` in `result_val_LambdaANF_Wasm` and `max_mem_pages` in `LambdaANF_to_Wasm.v`. Check whether `Codegen/LambdaANF_to_Clight_correct.v` has joined `theories/_CoqProject`, and whether `metarocq_anf_pipeline` still ends in `Admitted`.
- **Model exclusion.** Grep "allocation never fails" in CompCert `common/Memory.v`. Read the body of `mmalloc_partial` in `LowStar.Monotonic.Buffer.fsti`.
- **Rust.** Run `rustc -Zoom=panic` on an empty file. Run `support/probes/oom_probe.rs` in modes `push`, `try` and `hook`; expect SIGABRT, `Err(AllocError …)` followed by `CONTINUED`, and a caught panic. Re-read the doc comment on `handle_alloc_error`.
- **JVM.** Run `support/probes/OomProbe.java` in modes `heap`, `arraysize`, `stack` (three or more times per `-Xss`) and `direct`. Compare the messages with the strings in `universe.cpp`.
- **CakeML.** Check the release tarball's sha256, build `cake`, compile `cakeml_heap.cml` and `cakeml_stack3.cml`, and run with `CML_HEAP_SIZE=16` or `CML_STACK_SIZE=1`. Expect status 1 and 2 respectively.
- **Specifications.** Re-read JVMS §6.3, JLS §11.1.3, the `memory.grow` note in Wasm `instructions.rst`, and C++ [intro.compliance.general]/2.1. A change in the phrases "may be thrown at any time" or "within its resource limits" is the signal to look for.
