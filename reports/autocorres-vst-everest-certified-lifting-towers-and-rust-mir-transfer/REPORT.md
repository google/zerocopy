# Certified Multi-Stage Lifting Towers (AutoCorres, VST, Everest, Rupicola, and Lean `Std.Do`) and Their Transfer to Rust MIR

## Summary

Systems verification stacks avoid reasoning directly over raw byte-and-CFG machine states by interposing a **certified lifting tower**: composable syntax, local-state, arithmetic, and memory passes linked by machine-checked simulation or weakest-precondition (WP) theorems. Comparing five production architectures—seL4 `AutoCorres` (`seL4/l4v@b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`), CompCert/VST `floyd` (`PrincetonUniversity/VST@d50ac1969f9f6586621895eb043ccf08a165f731`), Project Everest (`Low*`, `HACL*`, `EverParse`), Bedrock2/Rupicola (`mit-plv/rupicola@cd89cf519551add249540db9f24aa97d8cc5d20f`), and Lean 4 `Std.Do` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`)—establishes which layers transfer cleanly into Anneal's zero-TCB `theory/` directory (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`) over Rust `Runtime(PostCleanup)` MIR and where Rust demands genuinely new abstractions:

1. **Zero-TCB layers that transfer cleanly to `theory/`**:
   - AutoCorres **`L1` (CFG-to-structured control/exception rewriting)**, **`L2` (local-slot tuple lifting)**, **`WA` (guarded word-to-`Nat`/`Int` abstraction)**, and **`TS` (monad strengthening into pure, reader, option, or state functions)**;
   - Bedrock2's **continuation-passing `dlet!` block WP** (`WeakestPrecondition.v`) with operational fallback at loops and calls;
   - HACL\*'s **width-parametric endianness and slice-splitting algebra** (`Lib.ByteSequence.fsti`) and EverParse/LowParse's **injective parser/serializer `pts_to_serialized` linear `trade` view exchange** (`LowParse.Pulse.Base.fst`);
   - Lean 4 `Std.Do`'s **semi-reducible `PredTrans.apply` predicate-transformer barrier**—re-expressed over `Init.Core` because `Std.Do` itself cannot be imported under Pass 1's `Init.*`-only lock and closed syntax allowlist.
2. **C/Low\* assumptions broken by Rust `Runtime(PostCleanup)` MIR**:
   - AutoCorres **`HL` (global Burstall–Bornat type-indexed split heaps)** fails on Rust generics, `#[repr(transparent)]`, same-type `split_at_mut` slices, and `zerocopy` byte-to-struct casts (`&[u8]` $\leftrightarrow$ `&T`);
   - CompCert/VST's untyped `Memdata.Undef` and global step-indexed `mpred` spatial entailments conflict with Rust's typed `MaybeUninit<u8>` vs. invalid-scalar UB distinction, `Operand.move` deinitialization, and `<50ms` Lean kernel `whnf` budgets;
   - C/Low\* stacks lack primitives for **Tree Borrows argument protectors** (`ReservedFrz`/`Unique`/`Disabled`/`ReservedIM`/`Cell`), **`Immediate.scalarPair` fat-pointer metadata** (`&[T]`, `&dyn Trait`), and **MIR `cleanup` unwind pads with drop elaboration**.

## Applicability

This report evaluates layer-by-layer transfer into Anneal's untrusted `theory/` stack over `Trusted.MirAst` and `Trusted.MirSemantics` (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, anchored in CI Pass 2 to `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`).

Target Pass 1 audit constraints (`trusted/audit/TrustedBoundary.lean:16-122, 177-228, 439-595`):

- **Zero-TCB `RepoOrigin` Isolation**: Pass 1 `theory/` modules may import only the 51 locked `Init.*` modules (`foundation-lock.json`), `Trusted.*`, and `theory/`—never `Std.*` or `Lean.*` (`.sysrootFoundation` is Pass 2-only).
- **Closed Axiom & Syntax Allowlist**: Only `{propext, Quot.sound, Classical.choice}` are admitted; preflight rejects `sorry`, `axiom`, `partial` (including `._unsafe_rec`), `unsafe`, `native_decide`, `bv_decide`, `grind`, `set_option`, `noncomputable section`, `module`, `scoped syntax`, `macro_rules`, and `meta def`, followed by standalone kernel replay at `trustLevel := 0`.
- **Statement-Origin Separation**: Locked target theorem statements (`CrateTheorem`, `UnitTheorem`, `BodyVerified`) reference only `Init.*`, `Trusted.*`, and captured `Mir.*` constants; all `Anneal.*` lifting layers erase at the adequacy boundary.

Examined upstream artifacts:

- **seL4 AutoCorres (`seL4/l4v@b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`, `tools/autocorres/`)** and Greenaway et al. (`10.1145/2594291.2594296`).
- **VST-Floyd (`PrincetonUniversity/VST@d50ac1969f9f6586621895eb043ccf08a165f731`)**, **CompCert (`AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`)**, and Cao et al. (`10.1007/s10817-018-9457-5`).
- **Project Everest**: **KaRaMeL (`FStarLang/karamel@6bd5918c7c518adbb973f75f23cdd0900acb7526`)**, **HACL\* (`hacl-star/hacl-star@f557259007db9933442dde10aa995c1b00bd3446`)**, and **EverParse (`project-everest/everparse@f3e4ce51d9b68593fd98472cadcdeb8b6abf388f`)**, plus Low\* (`10.1145/3110261`), HACL\* (`10.1145/3133956.3134043`), and EverParse (USENIX Security 2019).
- **Rupicola (`mit-plv/rupicola@cd89cf519551add249540db9f24aa97d8cc5d20f`)**, **Bedrock2 (`mit-plv/bedrock2@67b682a504041acd2cd678782ff2505983d7cd6f`)**, and Pit-Claudel et al. (`10.1145/3519939.3523706`).
- **Lean 4 `Std.Do` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `src/Std/Do/`)**.

## Findings

### 1. Architectural Taxonomy: Post-Hoc Lifting vs. Extraction vs. Relational Synthesis

`Basis: source + normative + derived`

| Stack | Direction & Mechanism | Trusted Computing Base (TCB) | Memory Framing Discipline | Arithmetic Model |
| :--- | :--- | :--- | :--- | :--- |
| **seL4 AutoCorres** (`seL4/l4v`) | **Bottom-up proof-producing lifting**: ML synthesizes `L1`–`TS` defs + proves `L1corres`..`ac_corres` in Isabelle kernel | C-to-SIMPL parser + C semantics (**0-TCB lifter**: every pass emits a kernel proof) | Per-type split-heap records (`HeapLift.thy`) + validity bitmaps | `WordAbstract.thy`: lifts `'a word` to `nat`/`int` with `WORD_MAX`/`UWORD_MAX` guards |
| **CompCert / VST** (`VST`, `CompCert`) | **Deep-embedded separation logic**: `semax` / `wp` (`floyd/Iris_WP.v`) over CompCert `Clight` AST | Coq kernel + `Clight` semantics | Step-indexed spatial `mpred` (`data_at`, `field_at`, `mapsto`, magic wand) | CompCert `Int`/`Int64`/`Ptrofs` modular words + Coq `Z` (`lia`) |
| **Project Everest** (`Low*`, `HACL*`, `EverParse`) | **Top-down shallow verification + unverified extraction**: F\*/Pulse (Z3) extracted via KaRaMeL to C/Rust | F\* typechecker + **Z3 SMT** + `HyperStack` + **KaRaMeL** | Coarse `B.loc` sets (`modifies`, `B.loc_disjoint`) or Pulse `slprop` + `trade` | `Lib.IntTypes`: `PUB` (`range_t`) vs. `SEC` constant-time integers |
| **Bedrock2 / Rupicola** (`rupicola`, `bedrock2`) | **Top-down relational compilation**: Coq tactics derive `bedrock2.cmd` + `WeakestPrecondition` proof from Gallina `nlet_eq` | Coq kernel + `bedrock2.Semantics` | First-order byte-map `map.split` (`(P * R)%sep mem`) | `coqutil` width-parametric `word` (`ZnWords` → `Z`) |
| **Lean 4 `Std.Do`** (`leanprover/lean4`) | **Shallow monad-morphism VCGen**: `WP m ps` maps `StateT`/`ExceptT`/`EStateM` into `PredTrans ps` | Lean 4 kernel (shallow Lean code only; no IR semantics) | State-tuple Heyting algebra `SPred σs` (`σ₁ → ... → ULift Prop`), non-spatial | Lean `UInt*`/`BitVec w` |

**Alignment with Anneal.** Anneal (`trusted/` capturing actual `rustc` `Runtime(PostCleanup)` MIR + untrusted `theory/` audited by `TrustedBoundary.lean`) shares AutoCorres's exact **zero-TCB lifter property** while avoiding Low\*/KaRaMeL's Z3+extractor TCB and Rupicola's requirement to rewrite pre-existing Rust crates in Gallina.

### 2. seL4 AutoCorres (`L1 -> L2 -> HL -> WA -> TS`): Layer-by-Layer Transfer to MIR

`Basis: source + derived`

Inspecting `tools/autocorres/{L1Defs,L2Defs,HeapLift,WordAbstract,TypeStrengthen}.thy` (`seL4/l4v@b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`) isolates four transferable passes and one broken assumption:

1. **`L1` — Control-Flow & Abrupt-Exit Structuring (`L1Defs.thy:16-66`)**: Rewrites SIMPL (`Skip`, `Basic`, `Cond`, `While`, `Throw`, `Catch`, `Call`) into `'s L1_monad = ('s, unit + unit) nondet_monad` (`Inr ()` normal, `Inl ()` abrupt exit caught by `L1_catch`). `L1corres check_term Γ A C` (`lines 55–65`) proves that if `¬ snd (A s)`, `C` never faults (`Fault`/`Stuck` → `False`) and every transition lies in `fst (A s)`. **MIR Transfer**: `Anneal.PureLift.BlockCfg` (`traceExitPath`, `findConvergenceBlock`, `ExecFlow.returned`) already implements `L1`-equivalent diamond convergence and early-return routing in computable Lean; extending `ExecFlow` with a third `.unwinding` pole covers MIR `cleanup` edges.
2. **`L2` — Local Variable Tuple Extraction (`L2Defs.thy:11-101`)**: Lifts unaddressed C stack locals into monadic bindings in `('t, 'e + 'r) nondet_monad` (`L2_seq`, `L2_gets`, loop-carried tuple `L2_while c A i`, `L2corres` over `corresXF`). **MIR Transfer**: In C, taking `&x` forces `x` onto the byte heap. Pairing `L2` with `PureLift` (`SymState.locals` + `PermTree`) lifts *both* unborrowed and safely borrowed MIR locals into pure tuples, dropping to spatial memory (`SpatialPin`) only on `&raw` / raw-pointer casts.
3. **`HL` — Burstall–Bornat Type-Split Heaps (`HeapLift.thy:17-151`)**: Splits raw C memory into one total function `heap_T :: T ptr => T` per C type `T` (`L2Tcorres`, `struct_rewrite_*`), giving free non-aliasing across distinct types `A ≠ B`. **MIR Transfer (`Fails on Rust`)**: Rust generics, `#[repr(transparent)]`, `&mut [u8]` $\leftrightarrow$ `&mut Header` (`zerocopy`), `MaybeUninit<T>` $\leftrightarrow$ `T`, and same-type `split_at_mut(&mut [u32])` routinely alias or reinterpret the same `(AllocId, Offset)` bytes across types or within one type. In AutoCorres this forces `no_heap_abs` (`README.md:122-123`) across the whole function; in Rust, `HL` must be replaced by **per-loan `PermTree` tries + `SpatialPin` heaplets**.
4. **`WA` — Guarded Word Abstraction (`WordAbstract.thy:14-173`)**: Lifts signed words to `int` (`sint`) and opt-in unsigned words to `nat` (`unat`) via `abstract_binop P f X X'` (`∀ a b. P (f a) (f b) → f (X' a b) = X (f a) (f b)`, `lines 114–117`), injecting `L2_guard (a + b ≤ UWORD_MAX TYPE('a))` on `+`/`*` and `a ≥ b` on `-` (`unat_abstract_binops`, `lines 165–172`). **MIR Transfer (`High Value`)**: Because Pass 1 bans `bv_decide` and `grind`, an opt-in `WordAbstract` pass in `theory/` lifting checked/non-wrapping `IntWidth` arithmetic to `Nat`/`Int` (while keeping bitwise/wrapping ops in `BitVec`) eliminates modular wrap-around noise in slice-bounds proofs.
5. **`TS` — Monad Type Strengthening (`TypeStrengthen.thy:63-200`)**: Specializes each lifted `L2_monad` function to `pure` (`TS_return`, total `'a`), `gets` (`TS_gets`, `'s => 'a`), `option` (`gets_theE`, `'s => 'a option`), or `nondet` (`README.md:142-145`). **MIR Transfer (`Essential`)**: Exporting verified pure/read-only MIR callees as pure Lean `Args → Val` / `Args → Option Val` functions with `@[simp]` bridge lemmas lets callers rewrite interprocedural calls in $O(1)$ without unfolding callee MIR CFGs.

### 3. CompCert Clight and VST-Floyd: `field_at`, Padding, and `Memdata.Undef`

`Basis: source + normative + derived`

Inspecting `CompCert@2685140bf72c959446981fb99b5e44a8975021bc` (`common/Memdata.v:209-324`) and `VST@d50ac1969f9f6586621895eb043ccf08a165f731` (`floyd/field_at.v:124-142`, `floyd/Iris_WP.v:6-38`) reveals two critical lessons:

1. **`Memdata.Undef` vs. Rust `MaybeUninit` and Move Deinitialization**: CompCert models memory cells as `Undef | Byte b | Fragment v q n` (`Memdata.v:209-212`), where loading `Undef` yields `Vundef`. In Rust (`Trusted/MirSemantics.lean:63-156`), reading an uninitialized byte at `u8` is immediate `FaultKind.undefined` (UB), *whereas* copying `AllocByte.uninit` inside `MaybeUninit<u8>` or struct padding is defined and preserves uninitialized status; moreover, `Operand.move` actively deinitializes non-ZST locals (`deinitMovedPlace = true`, leaving ZSTs `()` and 1-variant ZST enums initialized). Rust spatial cells must therefore distinguish `.init v`, `.rawByte UInt8`, and `.uninit` (`LoanGraph.lean:519-522`) plus pointer provenance (`Option AllocId`).
2. **VST's `field_at` (`field_at.v:124-142`) and Explicit Padding**: VST defines `field_at sh t gfs v p` with `Arguments field_at ... : simpl never` and `field_compatible` alignment/bounds side-conditions, unfolding struct `data_at` into field conjuncts *plus explicit padding `memory_block`s*. Tracking padding explicitly is mandatory for `zerocopy` (`IntoBytes` requires zero padding so uninitialized padding bytes never leak into `&[u8]`, whereas `FromBytes` tolerates padding). However, VST places *all* state inside step-indexed `environ -> mpred` (`Iris_WP.v:6-7`); without custom `elab` spatial cancellers (banned in Pass 1), spatial `field_at` predicates must stay lazy inside `SpatialPin`.

### 4. Project Everest (`Low*`, `HACL*`, `EverParse`): Framing, Limb Codecs, and `pts_to_serialized`

`Basis: source + normative + derived`

Inspecting `hacl-star@f557259007db9933442dde10aa995c1b00bd3446` (`lib/Lib.{Buffer,IntTypes,ByteSequence}.fsti`) and `everparse@f3e4ce51d9b68593fd98472cadcdeb8b6abf388f` (`lib/everparse/lowparse/{LowParse.Spec.Base,LowParse.Pulse.Base}.fst`):

1. **Coarse `modifies` vs. `PermTree` (`Lib.Buffer.fsti:21-190`)**: Low\* frames mutations via `modifies (loc b0 |+| loc b1) h1 h2` and `B.loc_disjoint` (`mut_immut_disjoint`, `lines 151–157`). On safe Rust borrows, `PureLift.PermTree` discharges disjointness computationally by `rfl`, avoiding Low\*'s $O(N^2)$ `loc_disjoint` proof obligations unless raw pointers enter `SpatialPin`.
2. **Endianness & Slice-Homomorphism Combinators (`Lib.ByteSequence.fsti:67-200`)**: `nat_from_intseq_{le,be}` and `nat_from_intseq_le_slice_lemma` (`nat_from_intseq_le b == nat_from_intseq_le (slice b 0 i) + pow2 (i * bits t) * nat_from_intseq_le (slice b i len)`, `lines 188–190`) port directly into 3-axiom `Init.*` Lean `theory/` modules with zero Z3 dependency.
3. **EverParse `pts_to_serialized` and Linear `trade` (`LowParse.Spec.Base.fst:36-65`, `LowParse.Pulse.Base.fst:12-40`)**: LowParse pairs `parser k t` (`parser_kind_injective`, `parse_strong_prefix`) with `serializer p` and defines:
   ```fstar
   let pts_to_serialized (#k: parser_kind) (#t: Type) (#p: parser k t)
     (s: serializer p) (input: slice byte) (#pm: perm) (v: t) : slprop =
     S.pts_to input #pm (bare_serialize s v)
   ```
   bridged by ghost `pts_to_serialized_{intro,elim}_trade`, which exchanges raw bytes `pts_to input #pm v0` for typed `pts_to_serialized s input #pm v` plus a linear **`trade`** (magic wand returning updated bytes when the typed view ends). **Critical Transfer to `PureLift`**: `SpatialCodec` (`LoanGraph.lean:536-541`) currently has only `decode_encode : ∀ v, decode (encode v) = some v` (value $\to$ bytes $\to$ value). Supporting `zerocopy` (`&mut [u8]` $\to$ `&mut Header` $\to$ `&[u8]`) requires the **dual byte-to-typed view loan**: decoding `bytes` into child loan `lid_hdr : &mut Header` whose `BackTarget` writes `putBytes oldBytes hdr'` back into `lid_bytes`, preserving untouched padding bytes (`get_put` + `put_get`) as a first-order computational `trade`!

### 5. Bedrock2, Rupicola, and Lean 4 `Std.Do`: Block-CPS WP and Pass 1 Isolation

`Basis: source + derived`

1. **Bedrock2 CPS `dlet!` WP (`bedrock2/WeakestPrecondition.v:13-125`) vs. Rupicola (`rupicola/Lib/Compiler.v:16-145`)**: Bedrock2 evaluates straight-line commands via continuation-passing `dlet! l := map.put l x v in post t m l` (`line 75`), avoiding substitution blowup across branches and falling back to `Semantics.exec`/`call` only on `cmd.while`/`cmd.call` (`lines 101–106`). Adding a Bedrock2-style block-CPS theorem over `Anneal.MirWp` collapses multi-statement MIR basic blocks into single `let`-chains without per-statement `fuel` stepping. Conversely, Rupicola's `compile_nlet_as_nlet_eq` synthesizes imperative code from Gallina `nlet_eq` terms and does not apply to post-hoc MIR verification.
2. **Lean 4 `Std.Do` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `src/Std/Do/`)**: `Std.Do` cannot be imported in Pass 1 `theory/` (`Std.*` is blocked by `RepoOrigin`, and `SPred.lean`/`PredTrans.lean`/`WP/Basic.lean` use banned `module`, `scoped syntax`, `macro_rules`, `@[grind =]`, and `meta def`). However, its ~150-LOC mathematical core (`SPred σs := SVal σs (ULift Prop)` and conjunctive `PredTrans`) uses only `funext`/`propext`, and `PredTrans.lean:77-79` documents a vital Lean 4.34.1 kernel optimization: wrapping `t.trans` in a **semi-reducible `def PredTrans.apply`** (and keeping `SPred.entails` semi-reducible, `SPred.lean:78`) stops the kernel from eagerly unfolding large state continuations during `isDefEq`!

### 6. Five Rust `Runtime(PostCleanup)` MIR Realities Requiring New Abstractions

`Basis: source + normative + derived`

1. **Safe `&T`/`&mut T` lifetimes and reborrows without type-split heaps**: Handled by `PureLift`'s `PermTree` + `BackTarget` loan graph.
2. **Tree Borrows two-stage argument protectors (`Miri/TreeBorrows/Permissions.lean:18-112`, `10.1145/3735592`)**: Protected `&mut T` arguments transition `Unique → Disabled` (not `Frozen`) on foreign reads (`line 79`) and `ReservedFrz true → UndefinedBehavior` on child writes (`line 86`), while `&UnsafeCell<T>` uses `ReservedIM`/`Cell`. `Adapter.m3SpatialModel` (`Adapter.lean:249-254`) must expand from 4 states to the 6-state `(Permission × isProtected)` lattice.
3. **`MaybeUninit<T>`, struct padding, and `Operand.move` deinitialization (`MirSemantics.lean:67-156`)**: Requires 3-state `CellVal` (`.init`, `.rawByte`, `.uninit`) + explicit struct-padding ranges.
4. **Wide/fat pointers (`Immediate.scalarPair` in `Miri/Interpreter/Immediate.lean:15-105`)**: Slice (`(ptr, len)`) and trait-object (`(ptr, vtable)`) pointers carry two `Scalar Prov` components with component-wise `clearProvenance`, breaking single-word pointer assumptions.
5. **Unwind `cleanup` landing pads and drop elaboration (`Miri/Interpreter/Unwind.lean:13-120`)**: Requires a `.unwinding` flow pole tracking `PayloadStore` and cleanup-edge loan/protector release.

### 7. Recommended 5-Layer Zero-TCB `theory/` Tower and Rubric Evaluation

`Basis: derived + source`

Combining the transferable mechanisms yields a minimal 5-layer `theory/` stack over `Trusted.MirSemantics`: **L0** (`MirWp` + Bedrock2 block-CPS `dlet!` + `Std.Do` semi-reducible `PredTrans.apply`) $\to$ **L1** (AutoCorres `L1` CFG/loop/3-pole unwind normalizer) $\to$ **L2** (`PureLift` `L2` local/loan-graph lifter + AutoCorres `TS` `@[simp]` pure-callee summaries) $\to$ **L3** (`SpatialPin` sub-splits + EverParse `pts_to_serialized` padding-aware byte-view trades + 6-state protected Tree Borrows) $\to$ **L4** (opt-in AutoCorres `WA` guarded `Nat`/`Int` arithmetic + HACL\* `ByteSequence` slice lemmas).

| System / Architecture | (T1) 0-TCB Bridge (`Pass 1` Rules) | (P1) Human Spec Auditability | (P2) Authoring & Day-2 Locality | (P3) Lean 4 `v4.34.1` Kernel & LSP (`<50ms`) | (P4) Heterogeneous Composability | (P5) Failure Legibility | (C1–C2) Conceptual Minimality |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **AutoCorres (`L1`–`TS`)** | **High** for `L1/L2/WA/TS`; **Fails** for `HL` on byte casts/generics. | **High**: `TS` + `WA` yield clean pure specs. | **High** under `TS`; brittle when `no_heap_abs` triggers. | **Good**: first-order monads reduce cleanly. | **Poor** at all-or-nothing `HL`/`no_heap_abs` boundary. | **Good**: explicit `L2_guard` conditions. | **High** once `HL` is replaced. |
| **VST-Floyd (`mpred` + `field_at`)** | **Moderate**: heavy step-indexed `mpred` in `Init.*`. | **Low–Moderate**: exposes shares & `field_compatible`. | **Moderate**: local frames, needs custom AC cancellers. | **Poor in Pass 1**: manual `sepConj` proofs without `elab`. | **High** on raw structs/padding; lacks Tree Borrows. | **Moderate**: large residual `mpred` goals. | **Moderate**: pervasive spatial overhead. |
| **Everest (`Low*` / `HACL*` / `EverParse`)** | **Low as extractor** (Z3+KaRaMeL TCB); **High** as ported `theory/` codecs. | **High** on `ByteSequence`/parsers; verbose `modifies6`. | **Poor** on $O(N^2)$ `loc_disjoint` without Z3 triggers. | **High** for pure `ByteSequence` + parser lemmas. | **Moderate**: strong on slices, no general Rust reborrows. | **Good** on parser kinds; opaque `modifies` failures. | **High** for `pts_to_serialized` + `trade`. |
| **Bedrock2 / Rupicola** | **High** for Bedrock2 CPS WP; **N/A** for Rupicola on existing MIR. | **Moderate**: concise `fnspec!`, invasive `nlet_eq`. | **High** on straight-line `dlet!`; manual loops. | **Very High**: `dlet!` prevents branch term duplication. | **Moderate**: word-only pointers, no borrows. | **High**: goals mirror source let-bindings. | **Very High**: <300-LOC CPS WP core. |
| **Lean 4 `Std.Do`** | **Blocked directly** in Pass 1; **High** when ~150-LOC core is ported. | **High**: clean `⦃P⦄ x ⦃Q⦄` triples. | **High** on monadic state; non-spatial `SPred`. | **Very High**: semi-reducible `PredTrans.apply` (`L79`). | **Low alone**: needs external loan + spatial layers. | **Good**: `PostShape` separates normal/except paths. | **High**: single `WPMonad` morphism. |
| **Proposed 5-Layer `theory/` Tower** | **Complete 0-TCB**: `Init.*` + 3 axioms; erases at `BodyVerified`. | **High**: pure `TS` + slice/endian Rust specs. | **High**: block `dlet!` + `@[simp]` `TS` call summaries. | **Optimal (`<50ms` LSP)**: semi-reducible `PredTrans` + lazy `SpatialPin`. | **Complete**: safe borrows + byte trades + `MaybeUninit` + Tree Borrows. | **High**: tagged `L2_guard` / `EvalOutcome` diagnostics. | **Minimal**: 5 orthogonal single-purpose passes. |

## Boundaries

- **AutoCorres2 (Isabelle2025 AFP fork noted in `seL4/l4v` `tools/autocorres/README.md:20-25`) is `not examined` at source level**: Analysis covers `seL4/l4v` `tools/autocorres` at `b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`.
- **Direct Pass 1 import of `Std.Do` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`) is `unsupported` by `TrustedBoundary.lean`**: Both `Std.*` imports and `Std.Do`'s `module`/`scoped syntax`/`@[grind =]`/`meta def` features are rejected in Pass 1 (`TrustedBoundary.lean:217-228, 442-575`).
- **Global type-split heaps (`AutoCorres` `HL`) are `known not to apply` to `zerocopy`-style Rust crates**: `FromBytes`/`IntoBytes` byte-to-struct casts, `#[repr(transparent)]`, and `split_at_mut` alias across and within types.
- **`ScalarPair` wide pointers, `cleanup` unwind edges, and 6-state protected Tree Borrows in `Trusted.MirAst` are currently `unsupported` on `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`**: Unmodeled MIR forms step fail-closed to `FaultKind.unsupported`, while their reference models reside in `vendor/lean-miri` (`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`).
- **End-to-end Lean 4 `v4.34.1` kernel replay times for the combined 5-layer tower on >1,000-LOC `zerocopy` crates remain `unknown`** pending `MirTy.ref` / slice capture benchmarks.

## Evidence

1. **seL4 AutoCorres (`seL4/l4v@b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`)** (`2026-11-19`, `Basis: source + documentation`): `tools/autocorres/README.md:112-232`; `L1Defs.thy:16-84`; `L2Defs.thy:11-101`; `HeapLift.thy:17-151`; `WordAbstract.thy:14-173`; `TypeStrengthen.thy:63-200`.
2. **VST & CompCert (`PrincetonUniversity/VST@d50ac1969f9f6586621895eb043ccf08a165f731`, `AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`)** (`2026-11-19`, `Basis: source`): `VST/floyd/field_at.v:124-142`; `VST/floyd/Iris_WP.v:6-38`; `CompCert/common/Memdata.v:30-44, 209-324`.
3. **Project Everest (`FStarLang/karamel@6bd5918c7c518adbb973f75f23cdd0900acb7526`, `hacl-star/hacl-star@f557259007db9933442dde10aa995c1b00bd3446`, `project-everest/everparse@f3e4ce51d9b68593fd98472cadcdeb8b6abf388f`)** (`2026-11-19`, `Basis: source`): `hacl-star/lib/Lib.Buffer.fsti:21-190`; `Lib.IntTypes.fsti:18-168`; `Lib.ByteSequence.fsti:67-200`; `everparse/lib/everparse/lowparse/LowParse.Spec.Base.fst:36-65`; `LowParse.Pulse.Base.fst:12-40`; `karamel/krmllib/{C.Loops,Spec.Loops}.fst`.
4. **Bedrock2, Rupicola, & Lean `Std.Do` (`mit-plv/bedrock2@67b682a504041acd2cd678782ff2505983d7cd6f`, `mit-plv/rupicola@cd89cf519551add249540db9f24aa97d8cc5d20f`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`)** (`2026-11-19`, `Basis: source`): `bedrock2/src/bedrock2/WeakestPrecondition.v:13-125, 164-220`; `rupicola/src/Rupicola/Lib/{Core.v:30-54,Compiler.v:16-145}`; `lean4/src/Std/Do/{SPred/SPred.lean:34-157,PredTrans.lean:40-251,WP/Basic.lean:54-125,Triple/Basic.lean:37-130}`.
5. **Anneal & `lean-miri` (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`)** (`2026-11-19`, `Basis: source`): `trusted/lean/Trusted/MirSemantics.lean:63-182`; `trusted/audit/TrustedBoundary.lean:177-228, 439-595`; `theory/Anneal/MirWp.lean:69-156`; `theory/Anneal/PureLift/{SpatialPin,Adapter,MirBridge}.lean`; `vendor/lean-miri/Miri/TreeBorrows/Permissions.lean:18-112`; `Miri/Interpreter/{Immediate.lean:15-105,Unwind.lean:13-120}`.
6. **Publications (`Basis: normative`)**: AutoCorres (`10.1145/2594291.2594296`), VST-Floyd (`10.1007/s10817-018-9457-5`), Low\* (`10.1145/3110261`), HACL\* (`10.1145/3133956.3134043`), EverParse (USENIX Security 2019), Rupicola (`10.1145/3519939.3523706`), Tree Borrows (`10.1145/3735592`).

## Revalidation

1. **Anneal Pass 1 `Std.Do` & tactic allowlist**:
   ```bash
   grep -n "RepoOrigin\|allowedTheoryTacticKinds" trusted/audit/TrustedBoundary.lean
   ```
   Check whether `RepoOrigin` still restricts Pass 1 to `Init.*` + `.repo` and excludes `bv_decide`, `grind`, and `Std.Do` syntax.
2. **Anneal `Trusted.MirAst` & `SpatialPin` view trades**: Inspect `trusted/lean/Trusted/MirAst.lean` and `theory/Anneal/PureLift/{SpatialPin,Adapter}.lean` on `joshlf/anneal` `main` for `MirTy.ref`, `ScalarPair` slices, `cleanup` unwind targets, `putBytes` reverse view codecs, and 6-state protected Tree Borrows tags.
3. **Lean `Std.Do` & `EverParse` `LowParse.Pulse`**:
   ```bash
   curl --http1.1 -fsSL https://raw.githubusercontent.com/leanprover/lean4/<tag>/src/Std/Do/PredTrans.lean | grep -n -C 4 "def apply"
   curl --http1.1 -fsSL https://raw.githubusercontent.com/project-everest/everparse/<sha>/lib/everparse/lowparse/LowParse.Pulse.Base.fst | grep -n -A 18 "let pts_to_serialized"
   ```
   Confirm whether `PredTrans.apply` remains a semi-reducible wrapper over non-spatial `SPred` and whether `LowParse.Pulse` retains `pts_to_serialized` + `trade`.
