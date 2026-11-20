# Destination passing, tail recursion modulo cons/context, and return-slot copy elision: invariants, compiler preconditions, and where a copy survives

## Summary

- **One invariant family underlies all the systems examined.** A *destination* (Minamide's hole, a DPS out-parameter, an OCaml TMC `(block, offset)` pair, a Koka constructor context, a Haskell `Dest r a`, a C/C++ `sret` slot, an MLIR out-param memref, a Swift `@out` address) is sound to write into instead of returning-then-copying when four obligations hold: **(D1) no read before the write** (the hole is filled before the enclosing value is observed), **(D2) at most one write** (write-once / linear use), **(D3) no escape** of the destination past the region or scope that owns it, and **(D4) early writes are unobservable** on every path where the original program would not have written (exceptions/unwinding, other threads, aliases visible to the callee or caller). Calculi discharge D1–D3 with types (affine hole types, linear `Dest` with ages, rank-2 regions); compilers discharge D1–D4 with syntactic position checks and alias/unwind analyses, and **fall back to an explicit copy (or to not transforming) whenever an analysis cannot prove D4**.
- **OCaml TMC** (`lambda/tmc.ml`) clones each `[@tail_mod_cons]` function into a destination-passing version taking `dst`/`offset` parameters and writes results with an initializing store. Calls inside `try ... with` are *not* in tail position, mutable `let`s are not specialized, and effect/atomic/array/`with`-record primitives are not destination contexts. On OCaml 5.4.0 the transformed `List.map` ran 1e7 elements in 0.49 s (median of 5) versus 7.62 s for the plain version, with identical allocation (3 words/element) and 347,948 KiB (≈ 340 MiB) lower peak RSS; under an 8 MiB OCaml stack limit the plain version overflowed at 1e6 elements while TMC did not.
- **LLVM call-slot optimization** (`MemCpyOptimizer.cpp`, `performCallSlotOptzn`) rewrites `call f(tmp); memcpy(dest, tmp)` into `call f(dest)` only when: `tmp` is a fixed-size alloca used only by the call and the copy; the copy covers all of `tmp`; call and copy are in the **same basic block**; `dest` is untouched in between; `dest` is a *writable object* (alloca, `noalias writable` argument, `byval`, or noalias-call result — **never a global**) and dereferenceable; an early write cannot be seen through unwinding (`dead_on_unwind`, alloca, or nounwind); alignment suffices; and alias analysis proves the call does not access `dest`. An 18-case IR probe gave identical outcomes on `opt` 19.1.7 and 21.1.8. At the pinned `main` revision a new fallback admits non-provably-dereferenceable destinations when the call is `willreturn`+`nounwind`; this is source-only (not executed).
- **C++ `out = make();` through a reference did not benefit from call-slot forwarding in any probed clang 19.1.7 variant**: the reference parameter was lowered without `noalias`/`writable`, so the temporary and `memcpy` remained even when `make` was `noexcept`. `return make();` instead forwards the caller's hidden return slot unchanged (C++17 guaranteed elision, N4659 [dcl.init]/17.6.1; SysV psABI hidden `%rdi` pointer returned in `%rax`).
- **MLIR and Swift make the fallback copy explicit**: `BufferResultsToOutParams` turns memref results into caller-allocated out-params and inserts `memCpyFn` copies unless the returned buffer is a hoistable allocation (and always for a second return of the same allocation); One-Shot Module Bufferize bufferizes a call operand out-of-place if it is read after the call, assumes external callees read and write every tensor operand, and skips boundary analyses for recursive functions. Swift `AddressLowering` "never creates copies except to replace explicit value copies" but inserts moves to compose aggregates and break phi interference.
- **Destination passing is not uniformly a peak-memory win (toy model only).** In a deliberately small region model written for this report, forwarding destinations through tail positions gives 1 live cell and 0 copies for any nesting depth (copy-on-exit: 2 cells, d+1 copies; fresh destination per scope: d+1 cells). For non-tail combine trees, caller-allocated destinations remove every copy but *raise* the peak (2h+1 vs h+3 cells for full binary trees of height h) because destinations are allocated at call entry rather than at return. This is a property of the toy model, not a measurement of any compiler.

## Applicability

The report concerns **destination-passing (out-parameter, hole-filling) code generation and copy elision** as specified in five formal treatments and as implemented in five production toolchains, compared on preconditions, fallbacks, and cost.

Examined subjects (exact revisions in `REPORT.json`):

| Subject | Revision examined | How used |
| --- | --- | --- |
| `ocaml/ocaml` `lambda/tmc.ml` | `main` at `d2a87472c63a51b737619cca7ce9147fe0bbf035`; tag `5.4.0` at `907eec0b75c5bcf0fe6da5f4b9f11c5c22995a16` | source (both); execution with the OCaml 5.4.0 native compiler |
| `llvm/llvm-project` `MemCpyOptimizer.cpp`, `AliasAnalysis.cpp`, MLIR `OneShotModuleBufferize.cpp`, `BufferResultsToOutParams.cpp` | `main` at `c7d7fe46c0b78c0fdf5a04d7eb1271e0240337f2`; `llvmorg-21.1.8` at `2078da43e25a4623cab2d0d60decddf709aaea28`; `llvmorg-19.1.7` at `cd708029e0b2869e80abe31ddb175f7c35361f90` | source (main, 21.1.8); execution with Debian `opt` 21.1.8 and 19.1.7 and clang 19.1.7 |
| `swiftlang/swift` `AddressLowering.cpp`, `CopyPropagation.cpp` | `509314b5ad018ede69b4fd58d2ca0ab8a019c0ed` | source only |
| `koka-lang/koka` `src/Core/CTail.hs`, `lib/std/core/inline/types-cctx.h` | `b66091b2a5a7ea20c5ed9498ad1e1f03caee9589` | source only |
| `tweag/linear-dest` `src/Compact/Pure/Internal.hs` | `0e7db2e6b24aad348837ac78d8137712c1d8d12a` | source only (requires a patched GHC; not built) |
| GCC `g++` | Debian package 15.2.0-14 | execution (C++ elision matrix) |

Relationship among subjects: the papers define the invariants; each toolchain is read as an *implementation* of some subset of them, and the report catalogs where each implementation proves the invariant, where it checks syntactically, and where it falls back to a copy. The comparison is per-mechanism, not a benchmark shoot-out across languages.

Version scope:

- **OCaml**: `lambda/tmc.ml` differs between `5.4.0` and the pinned `main` only in the list of primitives that are not destination contexts (newly listed `Pphyscomp`, `Pcheckbound`, extra atomic and float/boxed-int conversions); the transformation logic is identical, so the 5.4.0 execution results are taken to describe `main` as well. That extension rests on that diff, not on running `main`.
- **LLVM call-slot**: execution covers only Debian 19.1.7 and 21.1.8 builds. The `main` revision differs in `performCallSlotOptzn` (variable-length alloca sizing, the `willreturn` fallback, alignment-raising via `max`); behavior specific to `main` is labeled source-only.
- **MLIR, Swift, Koka, linear-dest**: source-only; no claim about runtime behavior beyond what the quoted code states.

Execution host class: x86-64 Intel Xeon @ 2.60 GHz (96 logical CPUs, ~236 GiB RAM), Debian userland, runs not pinned to cores, single run per configuration unless stated. All timing numbers are host-specific.

## Findings

### 1. The formal core: what each calculus proves about destinations

| Treatment | Destination representation | How D1–D3 are enforced | What is proved, and how | Stated limits |
| --- | --- | --- | --- | --- |
| Minamide, POPL 1998 | hole abstraction of type `(τ1, τ2) hfun` ("τ1 is the type of a hole and τ2 is the type of a resulting data structure") | hole abstractions have linear types, treated as **affine** ("values of linear types are permitted to be abandoned implicitly") | type soundness (Theorem 1, subject reduction + progress) on paper; correctness of compilation to destructive update by logical relations (Theorem 2: `M ↓ c iff M′ ↓ c`) | "the calculus we have considered does not include recursion"; runtime representation is "a pair of pointers to a data structure and its hole" |
| Shaikhha, Fitzgibbon, Peyton Jones, Vytiniotis, FHPC 2017 | every array-returning function "receives as its first parameter a pointer to memory in which to store the result"; `alloc t (λ r. t)` | shape translation computes result sizes before allocation; stack-like `alloc` scoping | Theorem 1: shape-translated expressions "do not require any heap memory allocation" (paper proof) | restricted source language F̃ (subset of F#) |
| Leijen & Lorenzen, POPL 2023 (extended JFP 2025) | first-class contexts with `(appctx) app (ctx E) e = E[e]` and `(appcomp) app (k1 • k2) e = app k1 (app k2 e)` | soundness of the Minamide-hole instantiation; a Perceus heap-semantics instantiation for in-place update | equational derivation; the generic algorithm has "only 4 equations"; "evaluation contexts are the maximum context possible" | in-place update requires uniqueness; non-linear control falls back to copying (see §3) |
| Allain, Bour, Clément, Pottier, Scherer, POPL 2025 | OCaml-style `(block, offset)` destinations in *DataLang* | relational separation logic on top of Simuliris/Iris; simulation parameterized by a calling-convention protocol | Theorem 8.4 `wf(ps) ∧ ps ⇝ pt ⟹ ps ⊒ pt`: termination-preserving behavioral refinement, mechanized in Coq | DataLang is first-order and has no exceptions or effect handlers in its syntax; the paper notes the property "may not hold in programs that use multishot continuations ... or multishot effect handlers" |
| Bagrel & Spiwack, OOPSLA 2025 (λd) | linear destinations with **modes = multiplicity × age**; ages `↑k` ("defined k scopes ago") and `∞` (contains no destinations) | multiplicity 1 forces exactly-once writes (D1, D2); ages forbid a destination flowing into a scope where it would outlive its owner (D3) | Theorems 6.1 (type preservation) and 6.2 (progress), mechanized in Coq: "about 7000 lines long, and contains nearly 500 lemmas"; axioms: functional extensionality, classical logic, indefinite description | "λd doesn't have recursion" |
| Bagrel, JFLA 2024 (`linear-dest`) | `data Dest r a = Dest Addr#` into a GHC compact region | linear arrows (`%1 ->`) plus `fromIncomplete :: Incomplete r a (Ur b) %1 -> Ur (a, b)`: only unrestricted (`Ur`) results leave the region, so no `Dest` escapes | none mechanized; API discipline relies on GHC's linear types | needs a custom GHC with compact-region primops (README of the pinned revision) |

Basis: documentation (papers as cited under **Evidence**) + source (`linear-dest` `src/Compact/Pure/Internal.hs` lines 150, 158, 226, 276–288).

**D4 is the gap between calculi and compilers.** None of the calculi above models unwinding or concurrency; Allain et al. state DataLang's coverage limits explicitly. Every production implementation below adds a D4 check (or a syntactic approximation of one) that has no counterpart in the formal treatment it cites.
Basis: derived from the table above and §§2–8.

### 2. OCaml TMC: mechanism and exact preconditions (`lambda/tmc.ml`)

**Representation.** "In the OCaml value model, interior pointers are not allowed", so a destination is a record `{var : Ident.t; offset; loc}` naming the block and the field index (lines 43–59). Writing is `Psetfield_computed(Pointer, Heap_initialization)` (lines 69–71), i.e. an *initializing* store. A pending constructor is allocated `Mutable` with `Lambda.dummy_constant` as a recognizable placeholder (lines 125–141). The DPS clone takes two extra leading parameters, `dst` (`Pgenval`) and `offset` (`Pintval`) (lines 63–67, 979–994), and is always `Curried` even if the source function is tupled (lines 986–990).

**Evaluation order (D4-like obligation for effects).** When the transformation delays a constructor past effectful code, it first let-binds every argument that is not a variable or constant: "we want to preserve the evaluation order of the other arguments of the constructor" (`delay_impure`, lines 95–109, 143–173).

**Linearity of delayed contexts.** Nested constructors are accumulated as a delayed linear context `dst.i <- C .`; if the same delayed context would be emitted at more than one TMC call site (e.g. both branches of an `if`), `ensures_affine` materializes it first to avoid duplicating constructor applications (lines 205–277, 331–338).

**Where TMC applies and where it does not:**

| Construct (in a `[@tail_mod_cons]` function) | Behavior | Lines |
| --- | --- | --- |
| `e1; e2`, `if`, `match`/`switch`, string switch, `let`, `let rec` | tail position propagates into the tail subterm | 594–638 |
| `let mutable` | "mutable bindings are not TMC-specialized" (body still traversed) | 602–606 |
| `try l1 with ...` | `l1` is "not in tail-call position (after it returns we need to remove the exception handler)" | 642–648 |
| static catch / `exit` | body *is* in tail position | 649–654 |
| constructor `Pmakeblock` with exactly one TMC-able argument | becomes a destination; other arguments let-bound | 794–823 |
| constructor with several TMC-able arguments and no unique `[@tailcall]` | compile-time error when the DPS version is needed (not when only the direct version is) | 736–793, 1008–1062 |
| effect/DLS primitives, atomics, `Pmakearray`/`Pduparray`, `{r with ...}` (`Pduprecord`), boxed-number ops, `lazy` blocks | not destination contexts ("we don't handle ...") | 865–892 |
| tail call to a function not specialized for TMC | warning 72 `Tmc_breaks_tailcall` **only if the callee is a local `Lvar`** missing from the specialization map; other callee forms take the silent `No_tmc` branch | 671–680, 719 |
| `[@tailcall false]` | explicit bailout: "we are (knowingly) leaving the dps calling convention" | 721–731 |
| `[@tail_mod_cons]` function with no TMC call | warning 71 `Unused_tmc_attribute` | 971–974 |

Basis: source.

**Generated code (execution, OCaml 5.4.0, `ocamlopt -c -dlambda`).** For `let[@tail_mod_cons] rec map f = function [] -> [] | x :: xs -> f x :: map f xs` the direct version allocates the first cell with `makemutable 0 (apply f ...) 24029` (24029 is the placeholder constant) and calls `map_dps block 1 f xs`; the DPS clone is (whitespace condensed):

```text
map_dps/325
  (function dst/334 offset/333[int] f/332 param/331 tail_mod_cons
    (if (isint param/331)
      (setfield_ptr(heap-init)_computed dst/334 offset/333 0)
      (let (block0_arg0/335 = (apply f/332 (field_imm 0 param/331))
            block/336 = (makemutable 0 block0_arg0/335 24029))
        (seq (setfield_ptr(heap-init)_computed dst/334 offset/333 block/336)
             (apply map_dps/325 block/336 1 f/332 (field_imm 1 param/331) tailcall)))))
```

Note `block0_arg0` is let-bound *before* the block is allocated, preserving the left-to-right effect of `f x` relative to the recursive call (the `delay_impure` rule above).
Basis: execution.

**Diagnostics observed (execution, OCaml 5.4.0):**

- A tree map `Node (tmap f l, f x, tmap f r)` is rejected: "this constructor application may be TMC-transformed in several different ways. Please disambiguate by adding an explicit [@tailcall] attribute ...", with both calls flagged "This call could be annotated." Adding `(tmap[@tailcall]) f r` compiles; the left recursion still consumes stack proportional to left depth.
- A recursive call under `try ... with Not_found -> []` is still routed to the DPS clone, but inside the handler, as a non-tail call; the compiler emits warning 51 `wrong-tailcall-expectation` ("expected tailcall") at that call. Stack use therefore grows per element through the handler frames.
- **Diagnostic gap (not a soundness issue):** `| [x] -> id_list [f x]` where `id_list` is a *module-level* function produces **no** warning 72, although in the DPS clone the call becomes `setfield_ptr(heap-init)_computed dst offset (apply (field_imm 0 (global Tmc_breaks!)) ...)`, i.e. a non-tail call. The identical code with `id_list` bound by a local `let` emits warning 72. The cause is the dispatch at lines 671–680 versus 719:

```ocaml
      match apply.ap_func with
      | Lvar f ->
          let specialized =
            try Ident.Map.find f ctx.specialized
            with Not_found ->
              if tail then
                Location.prerr_warning
                  (Debuginfo.Scoped_location.to_location apply.ap_loc)
                  Warnings.Tmc_breaks_tailcall;
              raise No_tmc;
          in
      ...
      | _nontail -> raise No_tmc
```

  The one extra frame is bounded (the callee returns), so the effect is a missing warning, not unbounded stack growth. Whether upstream regards this as a bug: unknown.
Basis: execution + source.

**Runtime cost (execution, OCaml 5.4.0 native, `List.map (fun x -> x+1)` over `List.init n`):**

| Variant | n | median wall s (5 runs) | minor words / element | median peak RSS (KiB) |
| --- | --- | --- | --- | --- |
| plain recursion | 1e6 | 0.1298 | 3.00 | 84,760 |
| `[@tail_mod_cons]` | 1e6 | 0.0477 | 3.00 | 50,316 |
| accumulate + `List.rev` | 1e6 | 0.0766 | 6.00 | 60,288 |
| plain recursion | 1e7 | 7.6239 | 3.00 | 819,204 |
| `[@tail_mod_cons]` | 1e7 | 0.4860 | 3.00 | 471,256 |
| accumulate + `List.rev` | 1e7 | 0.8361 | 6.00 | 587,176 |

With `OCAMLRUNPARAM=l=1M` (OCaml stack limit 1M words = 8 MiB), plain recursion raised `Stack_overflow` at n = 1e6 and succeeded at 1e5; TMC and `rev` succeeded at 1e6. Derived: the plain/TMC peak-RSS difference at 1e7 is 347,948 KiB ≈ 35.6 bytes per element of extra stack; TMC allocates exactly as many words as plain recursion and half as many as `rev`.
Basis: execution (command and raw output under **Evidence**).

Published comparisons (not re-measured here): Bour, Clément, Scherer measured the accumulate-and-reverse version "35% slower on lists of size 10" (OCaml 4.10 prototype); Allain et al. report one `List.map` run takes "between 7ns, for empty lists, and 89ms on lists with a million element" and that `nontail` beats `tmc` up to 10^4 elements (OCaml 5.1). TMC shipped in OCaml 4.14.0 (March 2022) per Allain et al.

### 3. Koka TRMC: uniqueness-guarded in-place filling, path copying otherwise

Koka's `src/Core/CTail.hs` cites Leijen & Lorenzen and emits a hidden `trmc` variant with an accumulator slot (lines 11–13, 109–113). The decision of how to treat contexts depends on the effect row:

```haskell
{-
we generate
- if the runtime can copy contexts (setContextPath)
  we always generate a single definition which is optimized a bit if the effect is affine for sure (alwaysAffine)
- otherwise, a single definition of the effect is affine for sure (alwaysAffine)
- or two definitions for multiple resumptions (isMulti)
-}
```

(lines 80–85), with `alwaysAffine = effectIsAffine teff` (line 115) and `needsMulti = not (useContextPath || alwaysAffine)` (line 121).

The runtime makes the D2/D4 check dynamic. `kk_cctx_apply` in `lib/std/core/inline/types-cctx.h` writes the hole in place only if the context root is uniquely referenced, otherwise it copies the path to the hole:

```c
  else if kk_likely(kk_block_is_unique(kk_ptr_unbox(acc.res,ctx))) {
    *kk_field_addr_ptr(acc.holeptr,ctx) = child;   // in-place update the hole with the child
    return acc.res;
  }
  #if !defined(KK_CCTX_NO_CONTEXT_PATH)
  else {
    kk_assert_internal(!kk_block_is_unique(kk_ptr_unbox(acc.res,ctx)));
    return kk_cctx_copy_apply(acc.res,kk_field_addr_ptr(acc.holeptr,ctx),child,ctx);  // copy the context path to the hole and compose with the child
```

(lines 52–59). When the effect is statically affine the compiler emits `kk_cctx_apply_linear`, which only asserts uniqueness (lines 65–72). This is the mechanism behind the paper's hybrid scheme: "detect at runtime if a context is unique, and fall back to copying only if required". Published cost: knapsack with non-linear control "about 25% at worst" slower (Leijen & Lorenzen; not re-measured).
Basis: source + documentation.

### 4. Haskell `linear-dest`: the type system is the only guard

At the pinned revision the public API (in `src/Compact/Pure/Internal.hs`) is:

```haskell
newtype Incomplete r a b = Incomplete (a, b)                                    -- line 150
alloc :: forall r a. (Region r) => Token %1 -> Incomplete r a (Dest r a)          -- line 158
fromIncomplete :: forall r a b. (Region r) => Incomplete r a (Ur b) %1 -> Ur (a, b)  -- line 226
data Dest r a = Dest Addr#                                                        -- line 276
fill :: forall lCtor (r :: Type) (a :: Type). (Fill lCtor a, Region r) => Dest r a %1 -> DestsOf lCtor r a
fillComp :: forall r a b. (Region r) => Incomplete r a b %1 -> Dest r a %1 -> b
fillLeaf :: forall r a. (Region r) => a -> Dest r a %1 -> ()
```

A `Dest` is a raw address (`Addr#`); D1/D2 come from the `%1` arrows, D3 from requiring `Ur b` before the structure becomes readable and from the region type variable `r` bound by `withRegion :: (forall r. Region r => Proxy r -> Token %1 -> Ur b) %1 -> Ur b` (line 134). There is no dynamic check. Published measurements (Bagrel 2024, AMD EPYC 7401P, single core): S-expression parser at 2^22 bytes input — "about 45% more allocations ... but uses 35% less memory at its peak, and ... spends 47× less time in garbage collection"; difference lists "slower (by a factor 2-4)".
Basis: source + documentation.

### 5. LLVM call-slot optimization: precondition catalogue

The transformation (comment at `MemCpyOptimizer.cpp` lines 832–844 on `main`):

```text
  //   call @func(..., src, ...)
  //   memcpy(dest, src, ...)
  // ->
  //   memcpy(dest, src, ...)
  //   call @func(..., dest, ...)
  // ... we additionally check that src only holds uninitialized values at the
  // moment of the call, meaning that the memcpy can be discarded rather than moved.
```

| # | Precondition (all must hold) | `main` lines | 21.1.8 lines | Probe case → outcome on opt 19.1.7 and 21.1.8 |
| --- | --- | --- | --- | --- |
| P1 | `src` is a fixed-size, non-scalable `alloca` | 846–860 | 862–880 | (all cases use an alloca) |
| P2 | copy size ≥ alloca size | 862–863 | 882 | G partial copy (32 of 64 B) → **kept** |
| P3 | call and copy in the same basic block ("block local restriction") | 874–877 | 894–897 | E cross-block → **kept** |
| P4 | `dest` not accessed between call and copy | 884–891 | 904–911 | C load from `dest` in between → **kept** |
| P5 | `dest` is a writable object and dereferenceable for the copy size | 904–922 | 927–933 | B1 `noalias sret` without `writable` → **kept**; F2 under-aligned alloca → elided |
| P5′ | (`main` only) if P5 fails, proceed when the call is guaranteed to transfer execution to the copy (`willreturn` + `nounwind`, nothing in between may trap) | 911–921 | absent | I plain pointer + willreturn callee → **kept on 21.1.8** (source-only for `main`) |
| P6 | early write invisible through unwinding: function `nounwind`, or `dest` is not visible on unwind (alloca, `byval`, `dead_on_unwind`), or no instruction in `[call, copy)` may throw | 924–941, 265–283 | 935–952, 268–286 | B3 `writable` but not `dead_on_unwind`, may-throw callee → **kept**; B2 (`dead_on_unwind`), B4 (nounwind callee), B5 (nounwind caller) → elided |
| P7 | `dest` alignment ≥ `src` alignment, or `dest` is an alloca (alignment is raised) | 943–951, 1068–1073 | 954–962 | F1 align-1 argument → **kept**; F2 align-1 alloca → elided, alignment raised to 8 |
| P8 | `src` used only by the call, the copy, lifetime markers, addrspacecasts | 953–972 | 964–983 | (structural) |
| P9 | if the callee may capture `src`: `dest` is function-local and not captured before the call, and nothing after the call (up to `lifetime.end`/return) may access `src` | 974–1021 | 985–1033 | D1 → elided; D1b unknown call after copy → **kept**; D2 `dest` escaped before call → **kept** |
| P10 | `dest` dominates the call (or is a constant-index GEP whose base does) | 1023–1034 | 1035–1046 | (structural) |
| P11 | AA proves the call does not mod/ref `dest` | 1036–1046 | 1048–1058 | H1 global `dest`, unknown callee → **kept** |

The thread-visibility case is acknowledged but unchecked: "4. If cpyDest is potentially captured, there may be accesses to it from another thread. ... TODO: This is currently not checked." (`main` lines 933–937).

**Globals are never call-slot destinations.** `isWritableObject` (in `llvm/lib/Analysis/AliasAnalysis.cpp`) states: "We don't consider globals as writable: While the physical memory is writable, we may not have provenance to perform the write." (21.1.8 lines 911–912; identical text at `main` lines 992–993). Arguments qualify only with both `writable` and `noalias` (21.1.8 lines 922–929). Probe H2 (global `dest`, callee `nounwind memory(argmem: write)`) and H3 (additionally `willreturn`) were **kept** on 21.1.8 accordingly. `isNotVisibleOnUnwind` accepts allocas, `byval` or `dead_on_unwind` arguments, and noalias-call results (the latter only if not captured before unwind; this sub-case is a `TODO` in `mayBeVisibleThroughUnwinding`) (21.1.8 lines 888–909).
Basis: source + execution (probe `callslot.ll`, 18 functions; identical results on both `opt` versions).

**C++ through clang 19.1.7 (`-O2 -std=c++17`, execution):**

| C++ function (`struct Big { long a[8]; }`, 64 B) | First parameter as lowered | memcpy after -O2 |
| --- | --- | --- |
| `void assign_ref_throw(Big& out) { out = make_may_throw(); }` | `ptr nocapture noundef nonnull writeonly align 8 dereferenceable(64)` | yes |
| `void assign_ref_nothrow(Big& out) { out = make_nothrow(); }` (callee `noexcept`) | same | yes |
| `void assign_ptr_nothrow(Big* out) { *out = make_nothrow(); }` | `ptr nocapture noundef writeonly` | yes |
| `Big forward_prvalue() { return make_may_throw(); }` | `ptr dead_on_unwind noalias writable sret(%struct.Big)` | no (slot forwarded) |
| `void init_local_then_use(void (*sink)(Big*)) { Big t = make_may_throw(); sink(&t); }` | — | no |

Derived explanation: references carry neither `noalias` nor `writable`, so P5 fails before P6 is consulted; `noexcept` does not help. The only clang-emitted parameters that satisfy P5+P6 are its own `sret` slots, which is exactly the guaranteed-elision path. The x86-64 code for `forward_prvalue` is `movq %rdi, %rbx; callq make_may_throw; movq %rbx, %rax`: the caller's hidden pointer is passed straight through and returned in `%rax`.
Basis: execution + derived.

### 6. C++17 guaranteed elision versus NRVO, and the SysV return slot

Normative text: N4659 (C++17 working draft) [dcl.init] 11.6/17.6.1: "If the initializer expression is a prvalue and the cv-unqualified version of the source type is the same class as the class of the destination, the initializer expression is used to initialize the destination object." (wording from P0135R1, Richard Smith, 2016-06-20). SysV x86-64 psABI v1.0, "Returning of Values": "If the type has class MEMORY, then the caller provides space for the return value and passes the address of this storage in %rdi as if it were the first argument to the function. ... This storage must not overlap any data visible to the callee through other names than this argument. On return %rax will contain the address that has been passed in by the caller in %rdi." The non-overlap sentence is the ABI-level form of D4 for the callee side; LLVM encodes the caller-side guarantee as `noalias` on `sret` parameters (clang output above), not as a property of `sret` itself (LangRef's `sret` text implies neither `noalias` nor `writable`).
Basis: normative.

Copy/move constructor calls counted at run time (`elide.cpp`; same counts at -O0 and -O2 unless noted):

| Function | clang 19 C++14 | clang 19 C++14 `-fno-elide-constructors` | clang 19 C++17 `-fno-elide-constructors` | g++ 15 C++17 |
| --- | --- | --- | --- | --- |
| `Big make_big() { Big b; ...; return b; }` (NRVO candidate) | 0 | 2 moves | 1 move | 0 |
| `return Big(Big(Big()));` (prvalue chain) | 0 | 4 moves | **0** | 0 |
| `return c ? x : y;` (two named locals) | 1 copy | 1 copy + 1 move | 1 copy | 1 copy |
| `Big x; if (c) return x; Big y; return y;` | 0 | 2 moves | 1 move | **1 move** (also at -O2) |
| `Pinned` (copy and move deleted) returned as prvalue | compile error in C++14 ("call to deleted constructor") | — | 0 (compiles) | 0 (compiles) |

Only prvalue initialization is guaranteed (it survives `-fno-elide-constructors` in C++17 and makes non-movable returns legal); NRVO is an implementation choice that differs between clang 19 and GCC 15 on the same source.
Basis: execution.

### 7. MLIR: caller-allocated out-params and out-of-place bufferization

`BufferResultsToOutParams.cpp` (`main`):

- Each memref result becomes an appended argument; results with layouts other than identity or fully dynamic are rejected: "cannot create out param for result with unsupported layout" (lines 108–114).
- At each `return`, if `hoistStaticAllocs` (static shapes) or `hoistDynamicAllocs` applies and the returned value is produced by an `AllocationOpInterface` op with a hoisting kind other than `None`, the allocation is replaced by the out-param (copy elided); "Repeated returns of the same allocation reuse the primary out parameter; copy its contents into the out parameter for this occurrence"; otherwise `options.memCpyFn(builder, op.getLoc(), orig, arg)` inserts a copy (lines 176–209). `memref.realloc`/`bufferization.clone` are kept ("Erasing them would discard the data they preserve", lines 183–185).
- Callers allocate the out-param with `allocationFn` before the call (lines 272–300); dynamically shaped results without recoverable sizes fail with "cannot create out param for dynamically shaped result" (lines 264–270).
- Public functions are skipped unless `modifyPublicFunctions`; external callees are skipped (lines 243–246, 323–327).

`OneShotModuleBufferize.cpp` (`main`), the calling convention in the file header (lines 31–36): "In the absence of conflicts within a FuncOp, the FuncOp's bbArgs may always be written to in-place. If a tensor operand of a CallOp is read after the CallOp, the operand of the CallOp must bufferize out-of-place." For external functions "the CallOp analysis conservatively assumes that each tensor OpOperand is both read and written" (lines 57–59); returned buffers of external functions are never known writable, and a returned view "may itself be writable but alias a read-only buffer, such as an arith.constant or a callee result" (lines 286–300); functions in call cycles get no boundary analysis ("We currently skip all function argument analyses for functions that call each other circularly", lines 552–556).
Basis: source. Execution: not measured (no `mlir-opt` on the host).

### 8. Swift: address lowering without implicit copies, and OSSA copy propagation

`AddressLowering.cpp` (header, lines 12–122): the pass maps opaque (address-only) SIL values to storage and "never creates copies except to replace explicit value copies (copy_value, load [copy], store)"; it "inserts moves (copy_addr [take] [initialize]) of owned values to compose aggregates [and] resolve phi interference"; for guaranteed values "this pass inserts neither copies nor moves". Storage is shared through four mechanisms: reused storage (enum payload, opened existential), def-projection (`struct_extract`), use-projection (an operand built directly into its aggregate's storage, "only an optimization but is essential for reasonable code generation"), and phi-projection. A `return` operand may project into the function's indirect result ("Return instructions can project into the return value", lines 1314–1316). A use-projection is accepted only if the storage and all opened archetypes dominate the value (`findProjectionIntoUseImpl`, `checkStorageDominates`, lines 1605–1702); function arguments, including `@out` results, "always dominate" (lines 1696–1698). A phi that would require re-materializing an `init_existential` on both sides is refused because "we can't create an address phi" (lines 1627–1658). When an operand is not projected, `initializeComposingUse` emits a `copy_addr` (take for non-trivial types) into the aggregate (lines 2038–2061); phi interference is resolved with parallel-move sequences through a temporary (lines 2321–2363).

`CopyPropagation.cpp`: the pass "is only sound when SIL is in ownership-SSA form" and returns immediately for non-OSSA functions (lines 13–19, 650–654); it bails out entirely for functions with more than 100,000 instructions (lines 488–490); `-Onone` uses the mandatory variant that preserves debug info and only rewrites copies of owned values (lines 562, 686–690); copies of lexical values are canonicalized separately because "canonicalization of the canonical def will respect deinit barriers but canonicalization of the copies should not" (lines 176–188).
Basis: source. Execution: not measured (no Swift toolchain on the host).

### 9. Cross-system matrix: who proves what, and the fallback

| System | D1/D2 (init-before-read, write-once) | D3 (no escape) | D4 (unwind / aliasing / threads) | Fallback when unproven |
| --- | --- | --- | --- | --- |
| OCaml TMC | syntactic: only constructor arguments in tail-modulo-cons position; one destination per constructor (ambiguity is an error) | block is heap-allocated and only reachable from the destination chain | `try` body excluded from tail position; effects/atomics excluded; evaluation order kept by let-binding | direct-style code (no transformation), plus warnings 71/72/51 |
| Koka TRMC | compiler-generated contexts | contexts are values | dynamic: `kk_block_is_unique` on the context root; non-affine effects get a multi-shot variant | copy the context path (`kk_cctx_copy_apply`) |
| `linear-dest` | linear types | `Ur` + region type variable | none needed (pure API) | none (ill-typed programs rejected) |
| LLVM call-slot | P1, P8 (src only used by call + copy) | caller owns `dest` | P4–P6, P9–P11 (AA, `dead_on_unwind`, `nounwind`; threads unchecked) | keep `memcpy` |
| C++17 | language rule for prvalues | caller-provided storage | psABI non-overlap rule | NRVO optional; otherwise copy/move constructor |
| MLIR out-params | one out-param per memref result | caller allocates | conflicts → out-of-place; external → read+write assumed | `memCpyFn` copy / out-of-place buffer |
| Swift AddressLowering | OSSA ownership | dominance of storage | guaranteed values never moved | `copy_addr [take]` move into aggregate or phi temp |

Basis: derived from §§2–8.

### 10. Toy model: peak watermark of copy-on-exit versus destination passing

**Explicitly a toy model written for this report; it is not a model of any examined compiler.** Terms are `Leaf` (one fresh value), `Node(kids, temps)` (evaluates kids in order, keeps their results live, allocates `temps` scratch cells, produces one fresh value) and `Fwd(kid)` (its value is the kid's value — a tail call). Every term evaluation opens a region popped at its end. Strategies: **CE** copy-on-exit promotion (allocate a parent cell, copy, pop); **DPSf** caller allocates a fresh destination before each sub-term, `Fwd` copies its kid's destination into its own; **DPSe** as DPSf but `Fwd` hands its own destination to its kid.

| Shape | CE (peak cells, copies) | DPSf | DPSe |
| --- | --- | --- | --- |
| `Fwd` chain, depth d = 1 / 8 / 64 | (2, 2) / (2, 9) / (2, 65) | (2, 1) / (9, 8) / (65, 64) | (1, 0) for every d |
| full binary `Node` tree, height h = 1 / 4 / 8, temps 0 | (4, 3) / (7, 31) / (11, 511) | (3, 0) / (9, 0) / (17, 0) | same as DPSf |
| same, temps 2 | (6, 3) / (9, 31) / (13, 511) | (5, 0) / (11, 0) / (19, 0) | same as DPSf |

Over 10,000 random trees (seed 1, depth ≤ 8): `peak(CE) − peak(DPSe)` ranged from −6 to +1 (+1 in 4,139 trees, ≤ 0 in 5,861); `peak(DPSf) − peak(DPSe)` ranged 0..8; CE performed exactly one copy per term and DPSe zero copies in all 10,000. Derived closed forms consistent with the table: chains — CE peak 2, copies d+1; DPSf peak d+1, copies d; DPSe peak 1, copies 0. Full trees of height h with t temps — CE peak h+3+t; DPS peak 2h+1+t; CE copies 2^(h+1)−1.

Interpretation within the toy model: destination passing removes the transient extra cell at scope exit and every copy, but it *extends the destination's lifetime back to call entry*. That wins when destinations are forwarded through tail positions (the TMC / `return prvalue` case) and can lose when many pending destinations are live at once in non-tail combinations. "DPS always lowers peak memory" is therefore not established by this model.
Basis: execution (toy model of region-scoped evaluation, not any real system) + derived.

### 11. Proof obligations for a small verified IR (derived)

For an IR with lexical regions, the three strategies discharge different obligations:

| Strategy | Obligations |
| --- | --- |
| Copy-on-exit promotion | (a) copy preserves the value (deep vs shallow per type); (b) nothing in the child region is referenced by the copied value after pop (otherwise dangling); (c) the meter accounts for the transient parent+child overlap at exit |
| Caller-allocated destination | D1–D3 as typing invariants (e.g. λd-style ages or an affine hole type); D4 for each effect the IR has (exceptions: destination dead or rolled back on unwind; concurrency: destination unshared until completion); region of the destination outlives the callee's region |
| Forwarding / guaranteed elision | as above, plus identity of storage across the forwarding chain (the destination received is the destination passed), and evaluation-order preservation for any arguments moved past effects (OCaml's `delay_impure` obligation) |

Mechanization costs on record: λd type safety ≈ 7000 Coq lines / ≈ 500 lemmas without recursion or effects (Bagrel & Spiwack); OCaml TMC refinement mechanized in Coq/Iris over a first-order, exception-free model language (Allain et al.; proof size not found); Minamide's soundness and compilation correctness are paper proofs.
Basis: derived + documentation.

### 12. Performance and resource levels

| Level | Value | Basis |
| --- | --- | --- |
| L1 authoring | OCaml: one attribute per function (`[@tail_mod_cons]`), disambiguation by `[@tailcall]`; Allain et al. list `List.map` code sizes tmc 5 lines vs tmc-unrolled 18, `base` 78, containers 55, batteries 29; λd proof ≈ 7000 Coq lines; LLM token/turn budgets: not measured | documentation |
| L2 toolchain build | OCaml/LLVM/Swift/Koka builds: not measured | — |
| L3 compile latency | cost of the TMC / call-slot / address-lowering passes: not measured | — |
| L4 generated code | OCaml 5.4.0: TMC 0.0477 s vs plain 0.1298 s at 1e6, 0.486 s vs 7.62 s at 1e7 (medians, this host); Minamide "about 15 - 40% improvement" (1998, ALPHA); Bagrel 2024 parser 0.55–0.65× time; Shaikhha 2017 "order of magnitude" vs F# | execution; documentation |
| L5 proof/certificate checking | Coq check time of the λd and TMC artifacts: not found / not measured | — |
| L6 memory | OCaml 5.4.0 peak RSS at 1e7: TMC 471,256 KiB, plain 819,204 KiB (≈ 35.6 B/element of stack, derived); Bagrel 2024: 35% lower peak memory; toy model (§10) peaks; binary sizes: not measured | execution; documentation; derived |

### 13. Human comprehensibility (C1) and conceptual simplicity (C2)

- **C1.** OCaml's opt-in attribute keeps the transformation local and auditable: the only nonlocal facts a reader needs are "which call is in tail-modulo-cons position" and "is the callee also `[@tail_mod_cons]`", and the compiler reports ambiguity with source locations. The silent cases are the readability hazards: `try` bodies (only warning 51 hints at it), and module-level callees in tail position (no warning 72, §2). LLVM's call-slot is invisible at the source level: whether `out = make()` copies depends on parameter attributes a C++ programmer does not write (`noalias`, `writable`, `dead_on_unwind`), so mental models such as "noexcept removes the copy" are wrong for references (§5). C++17's rule is the most predictable: a prvalue initializes its result object, and NRVO is explicitly not guaranteed (GCC and clang differed on one case in §6).
- **C2.** The same invariant (D1–D4) is enforced by five unrelated mechanisms: typing (λd, `linear-dest`), syntactic position (OCaml TMC, C++ prvalues), alias + unwind analysis (LLVM), ownership SSA + dominance (Swift), and dynamic uniqueness (Koka). A minimal universal abstraction is a *typed destination with an owning scope*: λd's ages generalize "tail position" (age `↑0` destinations may be filled in place) and "no escape" (age `∞` values carry no destinations), and a `dead_on_unwind` flag is exactly D4-on-unwind for an ABI slot. Unifying would move OCaml's syntactic rules and LLVM's attribute checks into one typing judgment; it would not remove the need for an alias-analysis fallback in an untyped IR such as LLVM's.
Basis: derived.

### 14. Validation of implementations (V1–V4)

- **V1 (spec adequacy).** OCaml has a dedicated test directory `testsuite/tests/tmc/` (`ambiguities.ml`, `semantic.ml`, `stack_space.ml`, `try_with.ml`, `usage_warnings.ml`, `tupled_function*.ml`, ...); LLVM has `llvm/test/Transforms/MemCpyOpt/callslot*.ll` (`callslot_throw.ll`, `callslot_deref.ll`, `callslot_noalias.ll`, ...); MLIR has `buffer-results-to-out-params*.mlir` and `one-shot-module-bufferize*.mlir`; Swift has `address_lowering*.sil` and `copy_propagation*.sil/.swift` — all at the pinned revisions. No spec-mutation or mutant-kill data were found for any of them: unknown.
- **V2 (lowering soundness).** The OCaml TMC transformation has a mechanized refinement proof for a model language (Allain et al.); the production `tmc.ml` features outside DataLang (exceptions, `Lstaticcatch`, tupled functions, attributes) are covered by tests only. Call-slot correctness rests on alias analysis; translation validation (e.g. Alive2-style checking) of the probe cases was not run here: not examined.
- **V3 (concurrency/crash).** LLVM's own comment marks the cross-thread visibility case unchecked (§5); OCaml TMC's initializing stores into freshly allocated blocks are not shared before completion in single-domain code; multi-domain OCaml 5 behavior of partially built TMC structures was not examined.
- **V4 (operator mental models).** No empirical study of programmer expectations about TMC or call-slot elision was found: unknown.

## Boundaries

- **Not examined:** Swift and MLIR runtime behavior (no toolchains on the host); Koka runtime measurements; building `linear-dest` (requires a patched GHC); OCaml multi-domain interaction with TMC; OCaml flambda; LLVM `main` execution (the `willreturn` fallback P5′ is source-only); Rust's MIR destination propagation and NRVO; GCC's internal return-slot optimization beyond the run-time counts in §6; Alive2 or other translation validation of the call-slot cases.
- **Unknown:** why plain recursion at n = 1e7 is ≈ 15× slower than TMC on OCaml 5.4.0 even though both allocate 3 words/element — the run was not profiled; scanning of the deep stack by each minor collection is a plausible but unverified explanation. Proof sizes for Allain et al.'s Coq development (not reported in the paper). Whether upstream OCaml considers the missing warning 72 for module-level callees a bug.
- **Known not to apply:** the formal results in §1 do not cover exceptions, effects, or concurrency (Allain et al. DataLang; λd has no recursion); they do not by themselves justify the production `try`/effect rules in `tmc.ml`. The call-slot probe results do not transfer to globals as destinations (never writable objects in either examined LLVM version).
- **Unsupported (by the subject):** OCaml TMC for arrays, `{r with ...}`, effects/DLS, atomics, and lazy blocks; MLIR out-params for memrefs with non-identity, non-fully-dynamic layouts; MLIR out-params for dynamically shaped results without size information.
- **Attractive conclusions not established:** (1) "destination passing always lowers peak memory" — contradicted in the toy model for non-tail combine trees (§10), and not measured on any real compiler; (2) "`noexcept` lets clang drop the temporary in `out = make()`" — false for references in clang 19 (§5); (3) "a verified TMC transformation means the OCaml compiler's TMC pass is verified" — the proof is for a model language and transformation, not for `lambda/tmc.ml`.
- The toy-model numbers in §10 are properties of that model only.

## Evidence

Observation date for all evidence: 2026-11-20 (source fetched from GitHub at the revisions below; executions on that date).

**Source (path; revision; lines):**

- `ocaml/ocaml` `lambda/tmc.ml` at `d2a87472c63a51b737619cca7ce9147fe0bbf035`: destination type 43–59; `assign_to_dst` 69–71; `Constr` placeholder 125–141; `delay_impure` 95–109, 143–173; delayed contexts 205–277; `ensures_affine` 331–338; two-pass design 353–381; tail propagation 594–660; `Lmutlet` 602–606; `Ltrywith` 642–648; `Lstaticcatch` 649–654; `choice_apply` 662–734 (warning 72 at 676–680, silent branch 719); `choice_makeblock` 736–823; unsupported primitives 865–892; `make_dps_variant` 968–997; error messages 1008–1062. Same file at `907eec0b75c5bcf0fe6da5f4b9f11c5c22995a16` (5.4.0): 1060 lines; `diff` against `main` shows only a constant-constructor representation change (line 134 of `main`) and primitive-list changes (lines 842, 852, 860–861, 868–869, 880 of `main`).
- `llvm/llvm-project` at `c7d7fe46c0b78c0fdf5a04d7eb1271e0240337f2`: `llvm/lib/Transforms/Scalar/MemCpyOptimizer.cpp` `mayBeVisibleThroughUnwinding` 265–283, `performCallSlotOptzn` 826–1092; `llvm/lib/Analysis/AliasAnalysis.cpp` `isNotVisibleOnUnwind` 969–990, `isWritableObject` 992–1018; `mlir/lib/Dialect/Bufferization/Transforms/BufferResultsToOutParams.cpp` 95–151, 153–224, 226–313, 315–340; `mlir/lib/Dialect/Bufferization/Transforms/OneShotModuleBufferize.cpp` 10–62, 282–305, 496–560.
- `llvm/llvm-project` at `2078da43e25a4623cab2d0d60decddf709aaea28` (llvmorg-21.1.8): `MemCpyOptimizer.cpp` `mayBeVisibleThroughUnwinding` 268–286, `performCallSlotOptzn` from 842 (dereferenceability bail-out 927–933); `AliasAnalysis.cpp` 888–937.
- `swiftlang/swift` at `509314b5ad018ede69b4fd58d2ca0ab8a019c0ed`: `lib/SILOptimizer/Mandatory/AddressLowering.cpp` 12–122, 1290–1316, 1564–1702, 2029–2066, 2318–2390; `lib/SILOptimizer/Transforms/CopyPropagation.cpp` 13–49, 170–190, 427–500, 555–575, 648–695.
- `koka-lang/koka` at `b66091b2a5a7ea20c5ed9498ad1e1f03caee9589`: `src/Core/CTail.hs` 11–13, 80–85, 109–145; `lib/std/core/inline/types-cctx.h` 47–118; `kklib/include/kklib.h` 1462–1466.
- `tweag/linear-dest` at `0e7db2e6b24aad348837ac78d8137712c1d8d12a`: `README.md`; `src/Compact/Pure/Internal.hs` 134, 150, 158, 180, 226, 276–288.
- Test directories listed in §14 were enumerated with the GitHub contents API at the same revisions.

**Literature (identity verified against Crossref/arXiv/publisher pages on 2026-11-20):**

- Y. Minamide, "A Functional Representation of Data Structures with a Hole," POPL 1998, pp. 75–84, DOI 10.1145/268946.268953.
- A. Shaikhha, A. Fitzgibbon, S. Peyton Jones, D. Vytiniotis, "Destination-Passing Style for Efficient Memory Management," FHPC 2017, pp. 12–23, DOI 10.1145/3122948.3122949.
- F. Bour, B. Clément, G. Scherer, "Tail Modulo Cons," JFLA 2021, arXiv:2102.09823.
- D. Leijen, A. Lorenzen, "Tail Recursion Modulo Context: An Equational Approach," PACMPL 7(POPL) 2023, pp. 1152–1181, DOI 10.1145/3571233; extended version, JFP 35, e22, 2025, DOI 10.1017/S0956796825100117.
- T. Bagrel, "Destination-passing style programming: a Haskell implementation," JFLA 2024, arXiv:2312.11257.
- C. Allain, F. Bour, B. Clément, F. Pottier, G. Scherer, "Tail Modulo Cons, OCaml, and Relational Separation Logic," PACMPL 9(POPL) 2025, Article 79, pp. 2337–2363, DOI 10.1145/3704915, arXiv:2411.19397.
- T. Bagrel, A. Spiwack, "Destination Calculus: A Linear λ-Calculus for Purely Functional Memory Writes," PACMPL 9(OOPSLA1) 2025, Article 89, pp. 253–279, DOI 10.1145/3720423, arXiv:2503.07489.
- R. Smith, P0135R1 "Wording for guaranteed copy elision through simplified value categories," 2016-06-20; N4659 (C++17 working draft) [dcl.init] 11.6 paragraph 17.6.1.
- System V Application Binary Interface, AMD64 Architecture Processor Supplement, Version 1.0, "Returning of Values" (gitlab.com/x86-psABIs/x86-64-ABI, `x86-64-ABI/low-level-sys-info.tex`).
- LLVM Language Reference Manual, parameter attributes `sret`, `noalias`, `writable`, `dead_on_unwind` (llvm.org/docs/LangRef.html, fetched 2026-11-20).

**Execution (all on 2026-11-20, host class in Applicability):**

- OCaml probe: `ocamlopt -version` → `5.4.0`. Build `ocamlopt -I +unix unix.cmxa -o tmc_probe tmc_probe.ml`; run `./tmc_probe {plain|tmc|rev} N` under `/usr/bin/time -f maxrss_kib=%M`, 5 repetitions; stack-limited runs with `OCAMLRUNPARAM='l=1M'`. Edge cases: `ocamlopt -c -w +A tmc_edge.ml`, `ocamlopt -c tmc_ambig.ml` (exit 2), `ocamlopt -c tmc_ambig_fixed.ml` (exit 0), `ocamlopt -c -w +A-70 tmc_breaks.ml` (no warning), `ocamlopt -c -w +A-70 tmc_breaks_local.ml` (warning 72), `ocamlopt -c -dlambda tmc_edge.ml`. The probe program is:

```ocaml
let rec map_plain f = function [] -> [] | x :: xs -> f x :: map_plain f xs
let[@tail_mod_cons] rec map_tmc f = function [] -> [] | x :: xs -> f x :: map_tmc f xs
let map_rev f l = let rec go acc = function [] -> List.rev acc | x :: xs -> go (f x :: acc) xs in go [] l
(* main: l = List.init n (fun i -> i); Gc.full_major (); time and Gc.minor_words around
   the selected map with f = (fun x -> x + 1); print "Stack_overflow" if raised *)
```

- LLVM call-slot probe: `callslot.ll` (18 functions A, B1–B5, C, D1, D1b, D2, E, F1, F2, G, H1–H3, I, each `call @produce*(ptr sret(%T) align 8 %tmp)` with `%T = type { [8 x i64] }` followed by `llvm.memcpy` of 64 bytes, attributes as in the §5 table); command `opt -passes=memcpyopt -S callslot.ll` with `/usr/lib/llvm-21/bin/opt` ("Debian LLVM version 21.1.8") and `/usr/lib/llvm-19/bin/opt` ("Debian LLVM version 19.1.7"; `captures(none)` spelled `nocapture`). Outcome per function as in the §5 table; both versions identical. Shared declarations and two representative cases (the others vary only the attributes, instructions, or block structure named in the §5 table):

```llvm
%T = type { [8 x i64] }
declare void @produce(ptr sret(%T) align 8 captures(none))
declare void @produce_nounwind(ptr sret(%T) align 8 captures(none)) nounwind
declare void @produce_nw_wr(ptr sret(%T) align 8 captures(none)) nounwind willreturn memory(argmem: write)
declare void @produce_argmem(ptr sret(%T) align 8 captures(none)) nounwind memory(argmem: write)
declare void @produce_argmem_wr(ptr sret(%T) align 8 captures(none)) nounwind willreturn memory(argmem: write)
declare void @produce_cap(ptr align 8)
declare void @use(ptr)
declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)
@g = global %T zeroinitializer, align 8

define void @A_local_alloca() {                      ; ELIDED: call receives %dest
  %dest = alloca %T, align 8
  %tmp = alloca %T, align 8
  call void @produce(ptr sret(%T) align 8 %tmp)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %dest, ptr align 8 %tmp, i64 64, i1 false)
  call void @use(ptr %dest)
  ret void
}
define void @B3_writable_may_unwind(ptr noalias writable align 8 dereferenceable(64) %out) {  ; KEPT
  %tmp = alloca %T, align 8
  call void @produce(ptr sret(%T) align 8 %tmp)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %out, ptr align 8 %tmp, i64 64, i1 false)
  ret void
}
```
- C++ probes: `clang++` "Debian clang version 19.1.7 (10.1+build1)" and `g++` "(Debian 15.2.0-14) 15.2.0", matrix `-std={c++14,c++17} × {-O0,-O2} × {"",-fno-elide-constructors}` over `elide.cpp`; `clang++ -std=c++17 -O2 -S -emit-llvm assign.cpp` and `-S` for assembly. Counts and IR attributes as in §§5–6.
- Toy model: `python3 watermark.py` (Python 3.13, deterministic, seed 1); output tables reproduced verbatim in §10. Core of the model (random-tree generator: `Leaf` with probability 0.2 or at depth 0, else `Fwd` with probability 0.4 of the remainder, else `Node` with 1–3 kids and 0–2 temps, `random.Random(1)`, depth 8):

```python
class Machine:   # one counter per open region; live = sum of all regions
    def __init__(s): s.regions=[[0]]; s.live=0; s.peak=0; s.copies=0
    def alloc(s, n=1): s.regions[-1][0]+=n; s.live+=n; s.peak=max(s.peak, s.live)
    def alloc_in_parent(s): s.regions[-2][0]+=1; s.live+=1; s.peak=max(s.peak, s.live)
    def push(s): s.regions.append([0])
    def pop(s): s.live -= s.regions.pop()[0]

def run_ce(t, m):                 # result ends as one cell in the caller's region
    m.push()
    if isinstance(t, Leaf): m.alloc()
    elif isinstance(t, Node):
        for k in t.kids: run_ce(k, m)
        m.alloc(t.temps); m.alloc()
    else: run_ce(t.kid, m)
    m.alloc_in_parent(); m.copies += 1; m.pop()

def run_dps(t, m, forward):       # caller has already allocated the destination
    m.push()
    if isinstance(t, Node):
        for k in t.kids: m.alloc(); run_dps(k, m, forward)
        m.alloc(t.temps)
    elif isinstance(t, Fwd):
        if forward: m.pop(); run_dps(t.kid, m, forward); return
        m.alloc(); run_dps(t.kid, m, forward); m.copies += 1
    m.pop()
# measure: CE = run_ce on a fresh Machine; DPSf/DPSe = m.alloc() (root destination), then run_dps
```

## Revalidation

- **OCaml TMC preconditions:** diff `lambda/tmc.ml` regions 594–660 (tail propagation), 662–734 (`choice_apply`), and 865–892 (excluded primitives) against a new revision; rerun `ocamlopt -c -w +A-70` on the two `id_list` variants in §2 to see whether warning 72 now covers module-level callees, and `OCAMLRUNPARAM='l=1M' ./tmc_probe plain 1000000` vs `tmc` for the stack property.
- **LLVM call-slot:** rerun `opt -passes=memcpyopt -S callslot.ll` with the new `opt` and compare the KEPT/ELIDED column; cases I and H3 discriminate whether the `willreturn` fallback (P5′) has shipped, and H2 whether globals have become writable objects. Re-read `isWritableObject` and the P6 block (`mayBeVisibleThroughUnwinding`).
- **clang reference lowering:** compile `assign.cpp` with `-O2 -S -emit-llvm` and check whether reference parameters gain `noalias`/`writable` or `assign_ref_nothrow` loses its `llvm.memcpy`.
- **C++ elision:** rerun the `elide.cpp` matrix; the prvalue-chain row under `-fno-elide-constructors` and the `Pinned` row are the normative discriminators; the `two_named` row tracks implementation-specific NRVO.
- **MLIR / Swift / Koka:** diff the quoted line ranges; for MLIR, `buffer-results-to-out-params-hosit-static-allocs.mlir` and `one-shot-module-bufferize-call-copy-before-write.mlir` are the narrowest upstream tests covering the copy decisions.
- **Toy model:** rerun `python3 watermark.py`; it only re-establishes properties of the toy model.
