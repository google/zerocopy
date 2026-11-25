# Formal Algebras of Object Geometry, Call ABI, and Cross-Language/Asm Seams Across Verified Systems

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Formalizing object layout, value representation, calling conventions, and cross-language or inline-assembly seams inside a verified compiler or program logic requires cleanly separating **object geometry** from **representation encoding** and **call transport**—while preserving the exact non-local invariants that prevent naive `(size, align)` tuples from serving as congruences. Across eight primary mechanized frameworks (`CompCert`, `CompCertO`, `CH2O`, `Cerberus`, `RefinedC`, `MiniRust`, `Vellvm`, `Bedrock2`) plus `rustc_abi` and Lean 4 ISA models (`Kraken`), together with a standalone zero-TCB `prelude` Lean `v4.34.1` formalization ([support/LayoutCallAbiAlgebra.lean](support/LayoutCallAbiAlgebra.lean)) and live compiler probes ([support/probe_results.json](support/probe_results.json)):

1. **Two-Judgment Factorization & Primary-Verifier Taxonomy:**
   Real systems cannot unify in-memory object geometry and parameter-passing ABI into one morphism. Instead, sound architectures factor them into:
   - An **environment-indexed object-geometry algebra** ($E \vdash \mathsf{geometry}(T, \sigma) = G$) combining total span, ABI alignment, unadjusted natural alignment, initialized/data span vs. padding (`dsize` / byte masks), variant taggers and discriminators, validity niches, and route-sensitive subobject projections (separating disjoint product coordinates from overlapping union coordinates).
   - A **stateful calling-convention category** ($E \vdash \mathsf{call}(S) = C$) operating over flattened or target-classified arguments, register/stack-bank state, and caller/callee-saved frame conventions (`CompCertO`'s Kripke `callconv` category with horizontal composition `@`, refinement preorder `ccref`, join `+`, and CKLR commutation; `rustc_target::callconv`'s `PassMode` + register-bank state monad).
2. **Exact Obstructions to Naive Compositionality (Mechanized & Live-Measured):**
   Four distinct algebraic obstructions defeat naive bottom-up composition on `(size, align)` alone:
   - **Itanium Tail-Padding Reuse (`dsize` vs. `sizeof`):** Two records with equal `(size = 8, align = 4)`—`UserDtor` (non-POD) and `PodEqual` (POD)—produce divergent outer sizes (`8` vs. `12`) and appended field offsets (`5` vs. `8`) under inheritance or `[[no_unique_address]]`, verified live in `g++ 15.2.0` and proved in `sizeAlign_not_layout_congruence`.
   - **Dynamic Extent Rounding & Padding Absorption:** Trailing unsized tails (`LayoutStrategy` in `MiniRust`) define dependent Kleisli functions $\sigma \mapsto \mathsf{alignUp}(\mathsf{alignUp}(\text{end}_{\text{pre}}, a_{\text{eff}}) + \sigma \cdot s_{\text{elem}}, \max(a_{\text{pre}}, a_{\text{eff}}))$, which can be strictly *smaller* than naive sum-of-sizes (`dynamicSize 1 = 8 < 9 = headSize + elemSize`, proved in `dynamic_extent_not_naive_sum`).
   - **Interior-Mutability Niche Suppression:** `rustc_abi::LayoutCalculator::layout_of_struct` resets `largest_niche = None` and widens `bool` (`0..=1`) to `u8` (`0..=255`) under `NicheOptimizations::Disabled`, doubling `Option<WrapCell>` (`2` B) relative to equal-sized `Option<PlainBool>` (`1` B) in `rustc 1.102.0-nightly` (`niche_suppressed_by_interior_mut`).
   - **Call-ABI Non-Functoriality & Stateful Sequence Sensitivity:** `#[repr(C)] I128C(u128)` lowers on SysV `x86_64` to `{ i64, i64 }` (`Cast`) whereas equal-`(size, align)` `#[repr(transparent)] I128T(u128)` lowers to `i128 noundef` (`Direct`), and stateful multi-argument register-bank allocation with atomic multi-register rollback is order-sensitive (`callAbi_not_geometry_functor`, `callAbi_not_argument_monoid`).
3. **Sub-Register Partial Lenses & Cross-Language Envelopes:**
   Narrow architectural writes exhibit **asymmetric lens laws**: byte/low-lane writes that preserve upper register bits (`putLowPreserve`) form Very Well-Behaved Lenses (`GetPut`, `PutGet`, `PutPut`) that frame upper bits cleanly, whereas zero-extending narrow writes (`putLowZeroHi`, such as AArch64 `W32 -> X64`, x86-64 `EAX -> RAX`, or VEX/EVEX 128-bit vector writes) satisfy `PutGet` and `PutPut` yet **refute `GetPut`** (`putLowZeroHi_refutes_getPut`) unless modeled over orthogonal minimal bit-slices with explicit upper-zeroing effects.
4. **Zero-TCB `prelude` Lean `v4.34.1` Mechanization & Data/Proof Split:**
   Separating proof-free carriers (`GeometryData : Type`) from `Prop`-valued invariants (`ValidGeometry : GeometryData → Prop` backed by computable boolean reflection `validGeometryBool_sound`) compiles cleanly in pure `prelude` + `Init.*` (`80` declarations checked in `962.82 ms` under `-DwarningAsError=true`, `0` banned tactics, `0` `_unsafe_rec`, `0` `noncomputable`, `[propext]` only), avoiding dependent-sigma WHNF proof-tuple overhead (`294.88 ms` unbundled vs. `352.61 ms` bundled across `120` iterated state steps).

## Applicability

This report documents primary compiler/verifier source analyses alongside standalone executable probes:

- **Formalized Compiler & Language Specifications (source-inspected):**
  - **CompCert** (`AbsInt/CompCert@71262a2fb1b7e6c586cdb8cb084467d48ebced1d`): `cfrontend/Ctypes.v`, `cparser/StructPassing.ml`, `common/AST.v`, `common/Memdata.v`, `backend/Locations.v`, `backend/Conventions.v`, `x86/Conventions1.v`, `aarch64/Conventions1.v`.
  - **CompCertO** (`CertiKOS/compcert@87a62d95cd24a44e3ecd5fefddc70a969a881bcb`, branch `compcerto`): `common/LanguageInterface.v`, `common/CallconvAlgebra.v`, `driver/CallConv.v`.
  - **CH2O** (`robbertkrebbers/ch2o@1afb3f615db053b741341e9bfd1d5c65bddea641`): `types/type_environment.v`, `abstract_c/natural_type_environment.v`, `memory/memory_trees.v`, `memory/memory_basics.v`.
  - **Cerberus** (`rems-project/cerberus@d6eab7d91994b232e49dc7151f5f867482350352`): `frontend/model/ctype.lem`, `frontend/model/mem_common.lem`, `memory/vip/common.ml`.
  - **RefinedC / Caesium** (`gitlab.mpi-sws.org/iris/refinedc@d057583986651a28047164581f05fbee3a83ed9d`): `theories/caesium/struct.v`, `theories/caesium/bitfield.v`.
  - **MiniRust** (`minirust/minirust@063d784186d3252bee242217f218223205c0b568`): `spec/lang/types.md`, `spec/lang/representation.md`, `spec/prelude/target.md`.
  - **Rust Compiler** (`rust-lang/rust@96be22caa35b5c36c3a6d00571915255cd32ffa5`): `compiler/rustc_abi/src/lib.rs`, `compiler/rustc_abi/src/layout.rs`, `compiler/rustc_target/src/callconv/mod.rs`.
  - **Vellvm** (`vellvm/vellvm@7f0610c38d829b79bf6e867edf410c9e6f928f98`): `src/rocq/Syntax/DynamicTypes.v`, `src/rocq/Syntax/TypToDtyp.v`, `src/rocq/Semantics/MemoryBytes.v`.
  - **Bedrock2** (`mit-plv/bedrock2@67b682a504041acd2cd678782ff2505983d7cd6f`): `bedrock2/src/bedrock2/Scalars.v`, `bedrock2/src/bedrock2/BasicCSemantics.v`.
  - **Kraken** (`AeneasVerif/kraken@c9aa45ee1b273892d7efa7bbf8a8a9391e17b2c0`): `Kraken/AArch64/Semantics.lean`.
- **Executed Toolchains (Linux `x86_64`):**
  - **Lean 4** `leanprover/lean4:v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) checking [support/LayoutCallAbiAlgebra.lean](support/LayoutCallAbiAlgebra.lean) (`prelude` + `Init.*` only).
  - **Rust** `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM `23.1.5`) and **g++** Debian `15.2.0-14` (`15.2.0`), executed via [support/probe_noncompositionality.py](support/probe_noncompositionality.py).
- **Model–system relation for the Lean development:** `Model–system relation: none proved.` The Lean theorems in [support/LayoutCallAbiAlgebra.lean](support/LayoutCallAbiAlgebra.lean) formalize abstract algebraic models and counterexample witnesses inspired by C++ Itanium ABI, `rustc_abi`, SysV `x86_64`, `CompCertO`, and `Kraken`; the links to real compilers are established via direct primary-source inspection and separate live `rustc`/`g++` execution in [support/probe_results.json](support/probe_results.json), not via a verified compiler extraction proof.

## Findings

### 1. Comparative Algebraic Anatomy Across Mechanized Verifiers

`Basis: source + documentation`

Mechanized verifiers split object layout, value representation, calling conventions, and sub-register state at sharply different boundaries. Table 1 synthesizes how ten surveyed systems factor these concerns.

| System | Environment & Layout Abstraction | Aggregate & Union Representation | Call-ABI Transport Carrier | Key Limitation / Abstraction Gap |
| :--- | :--- | :--- | :--- | :--- |
| **CompCert** (`71262a2f`) | Concrete `composite_env` recursive bit/byte calculator (`Ctypes.v:454-618`, `Member_plain` / `Member_bitfield`) | `Memdata.v:365-420` mixes raw `Byte` values with `Fragment v q m` multi-byte value fragments | Flattened scalar `xtype` signatures (`AST.v:152-171`) mapped via `loc := R mreg \| S slot pos ty` (`Locations.v:47-116`, `typesize ∈ {1, 2}`) | Struct/union by-value passing & returns are eliminated in unverified OCaml `cparser/StructPassing.ml:38-80` before Ctypes/Coq passes. |
| **CompCertO** (`87a62d95`) | Inherits CompCert `Mem`/`Genv.symtbl`; separates structural ABI from memory injections via `Commutes cc R1 R2` | Same `Memdata` carrier, parameterized per pass by Kripke `CKLR` relations (`Extends`, `Inject`, `VAInject`) | Kripke 2-morphism `callconv li1 li2` (`LanguageInterface.v:48-111`), factored as `cc_c_locset @ cc_locset_mach @ cc_mach_asm` (`CallConv.v:1-780`) | Built on scalar `c_query`/`locset_query` interfaces; assumes fixed C/Mach ABI signature homogeneity. |
| **CH2O** (`1afb3f61`) | Abstract typeclass interface `Env` + `EnvSpec` (`type_environment.v:7-67`, instantiated by `natural_type_environment.v:5-239`) over weakening `Γ₁ ⊆ Γ₂` | Bit-level tree `mtree K` (`memory_trees.v:6-40`): `MStruct` with explicit padding `pbit_indetify`; dual union `MUnion i` vs. `MUnionAll` | Closed function execution with typed values; does not model register/stack calling-convention lowering | Unions require explicit `union_reset` coercion (`memory_trees.v:190-198`) to collapse variant state back to raw bits. |
| **Cerberus** (`d6eab7d9`) | Parameterized tag map `tag_definitions` (`ctype.lem:83-88`, `flexible_array_member`), detached from implementation memory module | Pointer/byte-level object store (`impl_mem`, `VIP` provenance) tracking `Disjoint \| ExactOverlap \| PartialOverlap` (`mem_common.lem:12-15`) | C abstract-machine function arguments (`Ail` expressions); no target-ISA register/stack psABI algebra | Separates abstract object bounds from low-level psABI packing (`passMode`) and machine registers. |
| **RefinedC / Caesium** (`d0575839`) | Coercible `struct_layout` (`sl_members : list (option var_name * layout)`, explicit `None` padding holes) -> `(ly_size, ly_align_log)` (`struct.v:8-50`) | Bitwise field combinators `bf_cons`/`bf_slice`/`bf_update` (`bitfield.v:9-19`) + Lithium keyed separation logic | Source-level C function specs; calling convention left to compilation outside Caesium | Assumes C-like byte-aligned fields inside `struct_layout` with static alignment proof `sl_fields_aligned`. |
| **MiniRust** (`063d7841`) | Layout embedded directly in `Type` (`Tuple { sized_fields, sized_head_layout, unsized_field }`, `LayoutStrategy` DST Kleisli `types.md:30-179, 259-277`) | `Union { chunks: List<(Offset, Size)> }` preserving partial-byte data; `Enum` decoupling `tagger` from `Discriminator` tree; Galois `(encode, decode)` over `≤_defined` | Abstract MIR `Terminator::Call` over typed values; no psABI register/stack classifier | `Type` bundles field offsets rather than factoring pure layout computation from representation relations. |
| **`rustc_abi` & `callconv`** (`96be22ca`) | 3-way split: `LayoutData` (`FieldsShape`, `Variants`, `largest_niche`, `uninhabited`, `max_repr_align`, `unadjusted_abi_align`) vs. `BackendRepr` vs. `FnAbi` | Orthogonal `BackendRepr` (`Scalar`, `ScalarPair`, `SimdVector`, `Memory`); `NicheOptimizations::Disabled` mutates `Bool -> I8` (`layout.rs:566-590`) | `PassMode::{Ignore, Direct, Pair, Cast, Indirect, IndirectUnsized}` + stateful `ComputeCallConv` (`callconv/mod.rs:58-92, 689-745`) | Even `PassMode::eq_abi` explicitly requires comparing `LayoutData` separately (`max_repr_align`, `unadjusted_abi_align`). |
| **Vellvm** (`7f0610c3`) | Recursive static `typ` erased to `dtyp` (`DynamicTypes.v:43-47`); `DataLayout` applied at `TypToDtyp`/`MemoryBytes` | `memory_byte := dvalue_bv 8` (`BYTE_Pointer \| BYTE_I \| BYTE_Mixed 8`) separating field vs. alignment poison padding (`MemoryBytes.v:73-115`) | LLVM IR call instructions (`call`/`ret` over dynamic values); target psABI resides below LLVM IR | Models IR aggregate values rather than psABI eightbyte/HFA register packing or `byval`/`sret` lowering. |
| **Bedrock2** (`67b682a5`) | Flat word-addressed byte map (`word -> byte`, `Scalars.v:18-36`) parameterized by bitwidth `width` (`32`/`64`) | No language-level aggregate layout type; multi-byte structures live purely as derived separating-conjunction predicates (`Array`/`le_split`) | Low-level machine/compiler RISC-V word sequences at procedure calls (`BasicCSemantics`) | Assumes word-sized scalars/memory only; no rich source aggregate ABI rules. |
| **Kraken** (`c9aa45ee`) | ISA-level flat `DataMem := Mem 64` + explicit `Reg64s` / `StatusFlags` records (`Semantics.lean:39-149`) | Byte-level ISA memory; aggregate types sit above the assembly seam (in Rust/Charon/Aeneas) | Explicit partial-width register getters/setters (`setRegOrSp .W32` zero-extending to `.W64`, `Semantics.lean:128-135`) | Shows directly why narrow register writes break naive whole-register frame laws without zero-extension tracking. |

Three structural invariants stand out across all ten designs:

1. **Decoupling Type Geometry from Codegen Representation and Call ABI (`rustc_abi`):** `rustc_abi::LayoutData` explicitly notes (`compiler/rustc_abi/src/lib.rs:2255-2263`) that `BackendRepr` is orthogonal to `FieldsShape`/`Variants` (for example, `ManuallyDrop<Result<isize, isize>>` carries `ScalarPair` while still retaining inner variants), and `PassMode::eq_abi` (`callconv/mod.rs:94-98`) documents that comparing `PassMode` alone is unsound without comparing `LayoutData` fields such as `max_repr_align` (`i686-windows`) and `unadjusted_abi_align` (`aarch64-linux`/`arm`).
2. **Axiomatic Layout Monotonicity (`CH2O EnvSpec`):** Krebbers (`types/type_environment.v:39-67`) isolates layout computation behind an abstract typeclass `Env` satisfying fifteen axioms (`size_of_array`, `size_of_struct = sum_list (field_sizes Γ τs)`, `align_of_offset_of`, and environment-weakening monotonicity `Γ₁ ⊆ Γ₂ → size_of Γ₁ τ = size_of Γ₂ τ`). Because every theorem is parameterized by `{EnvSpec K}` universally, properties proved once hold across every concrete `Env` implementation (`natural_type_environment.v`).
3. **Factoring Calling Conventions into Kripke Categories (`CompCertO`):** Koenig and Shao (`common/CallconvAlgebra.v:31-560`, `driver/CallConv.v:1-780`) show that calling conventions behave not as functions of layouts, but as **2-morphisms (`callconv li1 li2`)** over a world type `ccworld` with identity (`1`), sequential composition (`@`), join (`+`), superposition (`&&`), and Kleene star (`*`). Crucially, `Commutes cc R1 R2 : ccref (cc @ R2) (R1 @ cc)` pushes compiler memory-injection CKLRs (`R1 + ... + Rn`) upstream past structural ABI transitions (`cc_c_locset @ cc_locset_mach @ cc_mach_asm`).

---

### 2. Algebraic Structure of Object Geometry (`geometry(T, σ)`)

`Basis: source + execution (Lean kernel check)`

For a formal geometry judgment $E \vdash \mathsf{geometry}(T, \sigma) = G$ to support general reasoning about offsets, padding, transmutation, DST tails, enums, and unions, `G` must carry a **fibered algebraic signature** rather than `(size, align)`:

$$\mathsf{Geometry}(T, \sigma) \;\triangleq\; \bigl(\text{dataSize}, \text{totalSize}, \text{align}, \text{unadjAlign}, \text{mask}, \text{niche/tags}, \text{proj} : \text{Route} \rightharpoonup (\text{Offset} \times \text{Geometry})\bigr)$$

#### 2.1 Product Atlases vs. Variant-Scoped & Overlay Coordinates

Route-sensitive projection `projectStep` ([support/LayoutCallAbiAlgebra.lean](support/LayoutCallAbiAlgebra.lean):279-294) distinguishes two fundamentally incompatible coordinate geometries (`record_siblings_disjoint`, `union_members_overlap_at_zero`, lines 310-327):
- **Records & Fixed Arrays (Disjoint Product Atlas):** Distinct field designators `.field i ≠ .field j` project onto disjoint sub-intervals inside `[0, totalSize)`, checked structurally by `spansAllNonOverlap` (`record_siblings_disjoint`). On disjoint intervals, Store/lens updates satisfy standard Put-Put commutation and disjoint framing (`byteSubLens`-style).
- **Unions & Tagged Enums (Coincident Overlay vs. Variant-Scoped Coordinates):** Distinct union members `.unionMember i ≠ .unionMember j` project onto overlapping intervals anchored at `offset = 0` (`union_members_overlap_at_zero`), refuting `spanNonOverlap`.
  - In `CH2O` (`memory_trees.v:32-40, 190-198`), union writes require an active-variant tag `(i)` or `union_reset` erasure to `MUnionAll`.
  - In `MiniRust` (`types.md:54-89`, `representation.md:313-434`), unions track preserved byte spans `chunks : List (Offset, Size)` (capturing padding holes inside `#[repr(C)]` unions) while enums decouple disjoint `tagger` write maps from `Discriminator` read trees (`encode ∘ decode ≤_defined id`, `decode ∘ encode = Some`).

#### 2.2 Dynamic Shape `σ` as a Dependent Kleisli Strategy

When `T` has an unsized tail (slice `[U]` with count $\sigma = n$ or trait object `dyn Trait` with vtable $\sigma = (s, a)$), geometry becomes a **dependent strategy** (`LayoutStrategy::Tuple { head, tail }` in `MiniRust` `types.md:159-168, 259-277`), formalized in [support/LayoutCallAbiAlgebra.lean](support/LayoutCallAbiAlgebra.lean):331-360:
$$\mathsf{tailOffset}(d) = \mathsf{alignUp}(\text{prefixEnd},\, a_{\text{eff}}), \qquad \mathsf{dynamicSize}(d, \sigma) = \mathsf{alignUp}(\mathsf{tailOffset}(d) + \sigma \cdot s_{\text{elem}},\, \max(a_{\text{prefix}}, a_{\text{eff}}))$$
where $a_{\text{eff}} = \min(\text{cap}, a_{\text{elem}})$ under `repr(packed(cap))`. Theorems `dynamicSize_align_dvd` and `dynamicSize_ge_payload` prove invariant divisibility and containment across all $\sigma \in \mathbb{N}$, while `dynamic_extent_not_naive_sum` proves that naive size addition fails because prefix tail padding absorbs small tails (`prefixEnd = 5, align = 4`: static head size is `8`, yet appending a `1`-aligned byte gives `dynamicSize = 8 < 9 = headSize + 1`).

---

### 3. Mechanized Non-Compositionality Obstructions

`Basis: execution (Lean kernel check) + execution (g++ 15.2.0, rustc 1.102.0-nightly)`

Table 2 summarizes four exact mathematical obstructions verified both in the Lean `v4.34.1` kernel and against live `g++ 15.2.0` / `rustc 1.102.0-nightly` compilation outputs.

| Obstruction | Equal Prefix / Input Carriers | Divergent Composite Result | Root Algebraic Cause | Witness (`Lean` + Compiler) |
| :--- | :--- | :--- | :--- | :--- |
| **Itanium `dsize` Tail-Padding Reuse** | `UserDtor` `(size=8, align=4)` vs. `PodEqual` `(size=8, align=4)` | Appending `uint8_t d` gives `DerivedNonPod` `size=8, off=5` vs. `DerivedPod` `size=12, off=8` (`NoUniqueMember` also `8, 5`) | Quotient `(totalSize, align)` erases `dataSize` (`nvsize`/`dsize = 5` vs. `8`); inheritance/attr inspects `dataSize` | `sizeAlign_not_layout_congruence` + live `g++ 15.2.0` ([support/probe_results.json](support/probe_results.json)) |
| **Interior-Mutability Niche Erasure** | `PlainBool` `(size=1, align=1)` vs. `WrapCell(UnsafeCell<bool>)` `(size=1, align=1)` | `Option<PlainBool>` = `1` B vs. `Option<WrapCell>` = `2` B | `UnsafeCell` disables `NicheOptimizations` globally (`bool -> u8`, `largest_niche = None`), non-covariant over validity | `niche_suppressed_by_interior_mut` + `rustc 1.102.0-nightly` `-Zprint-type-sizes` |
| **Newtype Call-ABI Invariance Failure** | `I128C(u128)` (`repr(C)`, `16 B, align 16`) vs. `I128T(u128)` (`repr(transparent)`, `16 B, align 16`) | SysV `x86_64` IR: `take_c({ i64, i64 })` vs. `take_t(i128 noundef)` | `repr(C)` inhibits scalar unpacking (`BackendRepr::Memory` -> `Cast`), while `#[repr(transparent)]` forwards `Scalar` -> `Direct` | `callAbi_not_geometry_functor` + `no_functor_of_sizeAlign_to_callAbi` + `rustc --emit=llvm-ir` |
| **Stateful Sequence Order Sensitivity** | Argument multiset `{I128C, u64}` with `gpLeft = 2` | `[I128C, u64] -> ([castPair, indirectStack], {0, 1})` vs. `[u64, I128C] -> ([direct, indirectStack], {1, 2})` | Register bank allocation is a stateful left-fold with all-or-nothing multi-register rollback, not a commutative monoid | `callAbi_not_argument_monoid` |

These witnesses prove that any algebraic layout interface satisfying modularity (`size_of_struct` / field extension) must carry **at least** `(dataSize, totalSize, align, unadjustedAlign, nicheSpec, reprKind)` in `G`, and `call(S)` must take the **sequence of full ABI descriptors** (`S = (ret, [args], cc, target)`), never merely quotiented `(size, align)` values.

---

### 4. Sub-Register Lenses, Status Invariants, and FFI/Asm Interface Algebras

`Basis: source + execution (Lean kernel check)`

Extending a formal ABI algebra across C FFI and inline assembly (`asm!`) exposes two structural mismatches between abstract machine values and ISA states:

1. **Asymmetric Sub-Register Lens Laws (`putLowZeroHi` vs. `putLowPreserve`):**
   An architectural register bank does not obey Cartesian product laws when accessed through multiple bit-width views (`SplitReg` in [support/LayoutCallAbiAlgebra.lean](support/LayoutCallAbiAlgebra.lean):561-595). Narrow writes that preserve untouched upper lanes (e.g., x86 `al`/`ax` within `rax`, or explicitly modeled `ymm` sub-slices) satisfy all three Very Well-Behaved Lens axioms (`putLowPreserve_getPut`, `putLowPreserve_putGet`, `putLowPreserve_putPut`) and commute with `getHigh` (`putLowPreserve_frames_hi`). By contrast, narrow writes that zero upper bits—such as `Kraken`'s AArch64 `Reg64s.setRegOrSp .W32` (`Semantics.lean:128-135`, zero-extending `32 -> 64` bits) or x86-64 `EAX -> RAX` and VEX/EVEX `128`-bit vector writes zeroing upper `YMM`/`ZMM` lanes—satisfy `PutGet` (`putLowZeroHi_putGet`) and `PutPut` (`putLowZeroHi_putPut`), yet **violate `GetPut`** (`putLowZeroHi_refutes_getPut`) and clobber `hi` unless decomposed into disjoint architectural leaf slices or tracked as explicit full-register transitions (`ZMM :> bottomhalf :> bottomhalf` paired with upper-clobber masks).
2. **Environment-Polymorphic Call/Asm Envelope Composition:**
   Separating target-machine exit state into `(retVal, calleeFrame, invFlags, scratch)` (`MachineState`, lines 598-621, matching `CompCert`'s `callee_save_loc` partition in `Conventions.v:192-199` and invariant ABI control state such as `DF = 0`, `vstart = 0`, `FPCR`), stability across an arbitrary family of admissible environments `Admissible : Env → Prop` (`StableAcrossEnvFamily`, formalized via universal quantification `∀ env, Admissible env → ...` rather than existential witnesses) composes transitively across mixed-language FFI and inline-assembly steps (`compose_env_frame_stable`). Combining this with `CompCertO`'s preorder category (`scId`, `scComp`, `scRef` verified in `scComp_id_left`, `scComp_id_right`, `scComp_assoc`, `scRef_trans`) yields associative vertical composition of heterogeneous calling conventions without locking the logic to a single target psABI.

---

### 5. Zero-TCB `prelude` Lean `v4.34.1` Engineering Tradeoffs

`Basis: execution (Lean kernel check)`

Mechanizing these algebraic carriers inside a strict `prelude` + `Init.*` Lean `v4.34.1` environment without `omega`, `bv_decide`, `native_decide`, `Classical.choice`, `Quot.sound`, or `._unsafe_rec` yields three measurable engineering patterns observed in [support/probe_results.json](support/probe_results.json):

1. **Unbundled Data/Proof Split Beats Dependent Sigma Under Reduction:**
   Separating `GeometryData : Type` from `ValidGeometry (g : GeometryData) : Prop` and linking them via computable boolean reflection `validGeometryBool_sound` allows functional geometry transforms (`stepG`) and equality checks to reduce in the kernel without carrying or rewriting `Prop` proof tuples inside WHNF (`294.88 ms` end-to-end Lean check on `120` iterated `Nat.rec` steps unbundled vs. `352.61 ms` with dependent `{g // ValidG g}` wrapping, while requiring `0` axioms beyond `[propext]` on the structural proofs and `[]` zero axioms on `alignUp_dvd`, `sizeAlign_not_layout_congruence`, `niche_suppressed_by_interior_mut`, `callAbi_not_argument_monoid`, `scComp_assoc`, and `compose_env_frame_stable`).
2. **Direct `Nat.ble` / `Nat.beq` Recursion Eliminates `Decidable` Synthesis in Kernel Proofs:**
   Replacing `Nat.max` / `if a ≤ b` (which routes through `Decidable` instance resolution and triggers `if_pos`/`if_neg` rewrites) with direct `match Nat.ble a b` (`natMax`, `natMin`) and explicit `@Nat.rec` bounds (`alignUp_dvd`, `alignUp_ge`) compiles cleanly in `prelude` + `Init.*` with zero `omega` tactics and `861–963 ms` total check time for `80` declarations under `-DwarningAsError=true`.

## Boundaries

- **Known Not to Apply — `(size, align)` Congruence & Order-Invariance:** Modeling aggregate append, `#[repr(C)]` vs. `#[repr(transparent)]` parameter passing, or multi-argument register assignment as homomorphisms out of `(size, align)` **is known not to apply** to C++ Itanium layouts (`g++ 15.2.0`), Rust enum niches with `UnsafeCell`, or SysV `x86_64` ABI lowering (`rustc 1.102.0-nightly`).
- **Known Not to Apply — Standard Lens `GetPut` on Narrow Zero-Extending Registers:** Modeling narrow register writes (`W32 -> X64`, `EAX -> RAX`, VEX `XMM -> YMM`) as naive Very Well-Behaved Lenses over a single wide register **is known not to apply** because zeroing the upper half violates `GetPut` (`putLowZeroHi_refutes_getPut`).
- **Unsupported — By-Value Composite Calling Conventions Inside Coq `CompCert` (`71262a2f`):** CompCert's Coq intermediate languages (`Cminor`–`Asm`) and `Locations.loc` do not directly represent aggregate ABI classification; struct/union by-value arguments and returns are lowered earlier in unverified OCaml (`cparser/StructPassing.ml`).
- **Not Examined — Objective-C / Swift Witness-Table ABIs, CHERI Capability Tag Compression Proofs, and LLVM `MachineIR` Translation Validation:** Witness-table dynamic dispatch layouts beyond Rust `DynMetadata` / C++ vptrs, CHERI Morello `CapabilitiesGS.v` compression invariants inside Coq/Cerberus, and full LLVM backend ABI lowering after IR generation were **not examined**.

## Evidence

### Standalone Mechanized Probes & Live Compiler Receipts

All artifacts are self-contained inside [support/](support/) and verified directly on Linux `x86_64`:
- **[support/LayoutCallAbiAlgebra.lean](support/LayoutCallAbiAlgebra.lean)** (`623` lines, `prelude` + `Init.{Core, NotationExtra, Data.Nat.Basic, Data.Nat.Div.Basic, Data.List.Basic, SimpLemmas}`): Checked with `lean -DwarningAsError=true` (`leanprover/lean4:v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`) in `962.82 ms`. Audit across all `80` declarations confirms `0` `sorry`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `_unsafe_rec`, `0` `noncomputable`, `0` `Classical.choice`, `0` `Quot.sound`, and max axiom closure `["propext"]`.
- **[support/probe_noncompositionality.py](support/probe_noncompositionality.py)** (`212` lines) & **[support/probe_results.json](support/probe_results.json)**: Reproduces the Lean kernel check, `#print axioms` audit, unbundled vs. bundled `120`-step reduction timing (`294.88 ms` vs. `352.61 ms`), live `g++ 15.2.0` (`-std=c++20 -O2`) Itanium `dsize` measurements (`UserDtor` `[8, 4]` vs. `PodEqual` `[8, 4]`, `DerivedNonPod` `[8, 4, offset=5]` vs. `DerivedPod` `[12, 4, offset=8]`, `MemberNonPod` `[12, 4, offset=8]` vs. `NoUniqueMember` `[8, 4, offset=5]`), and live `rustc 1.102.0-nightly` (`3ef0c22cd`, LLVM `23.1.5`, `--edition=2024 -O --emit=llvm-ir` and `-Zprint-type-sizes`) measurements (`take_c({ i64, i64 })` vs. `take_t(i128 noundef)`; `Option<PlainBool>` `1 B` vs. `Option<WrapCell>` `2 B`).

### Primary Repository Citations

- `AbsInt/CompCert@71262a2fb1b7e6c586cdb8cb084467d48ebced1d`: `cfrontend/Ctypes.v:439-618`, `cparser/StructPassing.ml:31-80`, `common/AST.v:152-171`, `common/Memdata.v:365-420`, `backend/Locations.v:47-154`, `backend/Conventions.v:192-199`, `x86/Conventions1.v:218-275`, `aarch64/Conventions1.v:34-180`.
- `CertiKOS/compcert@87a62d95cd24a44e3ecd5fefddc70a969a881bcb`: `common/LanguageInterface.v:48-111`, `common/CallconvAlgebra.v:31-560`, `driver/CallConv.v:1-780`.
- `robbertkrebbers/ch2o@1afb3f615db053b741341e9bfd1d5c65bddea641`: `types/type_environment.v:7-67`, `abstract_c/natural_type_environment.v:5-239`, `memory/memory_trees.v:18-40, 184-250`.
- `rems-project/cerberus@d6eab7d91994b232e49dc7151f5f867482350352`: `frontend/model/ctype.lem:34-88`, `frontend/model/mem_common.lem:12-43`.
- `gitlab.mpi-sws.org/iris/refinedc@d057583986651a28047164581f05fbee3a83ed9d`: `theories/caesium/struct.v:8-55`, `theories/caesium/bitfield.v:7-20`.
- `minirust/minirust@063d784186d3252bee242217f218223205c0b568`: `spec/lang/types.md:20-346`, `spec/lang/representation.md:248-434, 623-805`, `spec/prelude/target.md:9-46`.
- `rust-lang/rust@96be22caa35b5c36c3a6d00571915255cd32ffa5`: `compiler/rustc_abi/src/lib.rs:1701-1890, 2032-2285`, `compiler/rustc_abi/src/layout.rs:285-342, 405-594, 800-941`, `compiler/rustc_target/src/callconv/mod.rs:58-98, 653-745`.
- `vellvm/vellvm@7f0610c38d829b79bf6e867edf410c9e6f928f98`: `src/rocq/Syntax/DynamicTypes.v:43-47`, `src/rocq/Semantics/MemoryBytes.v:73-118`.
- `mit-plv/bedrock2@67b682a504041acd2cd678782ff2505983d7cd6f`: `bedrock2/src/bedrock2/Scalars.v:21-36`.
- `AeneasVerif/kraken@c9aa45ee1b273892d7efa7bbf8a8a9391e17b2c0`: `Kraken/AArch64/Semantics.lean:39-149`.

## Revalidation

1. **Re-run the complete Lean + compiler probe (`< 3 s`):**
   ```bash
   python3 reports/formal-layout-call-abi-and-ffi-boundary-algebras/support/probe_noncompositionality.py
   ```
   (Set `LEAN_BIN=/path/to/lean` if Lean `v4.34.1` is not default on `PATH`.) Confirm exit code `0`, `hygiene_hits` all `0`, `distinct_axioms` at most `["propext"]`, and unchanged `cpp_probe` / `rust_probe` divergences.
2. **Re-check `rustc_abi` & `MiniRust` invariants:** Inspect `LayoutData`, `NicheOptimizations::Disabled`, and `PassMode::eq_abi` in `rust-lang/rust` (`compiler/rustc_abi/src/layout.rs` and `compiler/rustc_target/src/callconv/mod.rs`) plus `Type::layout` / `encode` / `decode` in `minirust/minirust` (`spec/lang/{types,representation}.md`) on newer releases (e.g., if MCP#1007 alters `ScalarPair` layout or `rustc` removes `inhibit_newtype_abi_optimization` differences).
3. **Re-run corpus validation:**
   ```bash
   python3 -B tools/reference.py catalog && python3 -B tools/reference.py check
   ```
