/-!
# Soundness of `rustc` 5-Category Static ELF Section Placement and Edition 2024 `#[unsafe(...)]` Attributes

Standalone kernel-checked formalization (`Lean v4.34.1`, core Lean only,
`0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`,
`0` `partial def`, `0` `._unsafe_rec`):

1. **Five-Category `(interiorMut, hasReloc, isZero)` Static ELF Section Classifier**
   modeling `intern_const_alloc_recursive` (`rustc_const_eval/src/interpret/intern.rs`),
   `codegen_static_item` (`rustc_codegen_llvm/src/consts.rs`), and
   `TargetLoweringObjectFile::{isSuitableForBSS, getKindForGlobal}` +
   `TargetLoweringObjectFileELF` (`llvm/lib/Target/TargetLoweringObjectFile.cpp`,
   `llvm/lib/CodeGen/TargetLoweringObjectFileImpl.cpp`) across `.pic` and `.staticModel`.
2. **Two-Phase ELF Loader, `PT_GNU_RELRO` Hardware Memory-Protection Semantics, and
   Soundness Theorems**:
   - Every dynamic relocation writes into a `WA` (`rw`) page pre-RELRO (`reloc_phase_targets_wa_and_succeeds`);
   - Every well-typed runtime interior mutation (`UnsafeCell` / `Atomic` / `static mut`)
     targets a `WA` (`rw`) page post-RELRO (`runtime_writes_target_wa_and_succeeds`);
   - Every frozen immutable static (`.rodata` unconditionally; `.data.rel.ro` post-RELRO)
     resides strictly in read-only memory (`ro`), preserves its relocated contents across
     arbitrary sequences of well-typed runtime steps, and traps with `sigsegv` on stray writes.
3. **Misclassification & Linker-Contamination Counterexamples**:
   - `.rodata` write trap on `UnsafeCell` (`ce1_rodata_write_trap_on_unsafecell`);
   - `.rodata` relocation trap on `&A` under PIC (`ce2_rodata_relocation_trap_on_pic_imm_ref`);
   - `.bss` (`NOBITS`) data loss on non-zero initializer (`ce3_bss_data_loss_on_nonzero_init`);
   - `#[unsafe(link_section = ".rodata")]` on an `UnsafeCell` static contaminating output
     `.rodata` flags to `WA` (`ce4_link_section_rodata_contaminates_segment`).
4. **Edition 2024 `#[unsafe(no_mangle)]` / `#[unsafe(export_name)]` / `#[unsafe(link_section)]`
   Safety Policy & Codegen Equivalence** (`rustc_attr_parsing/src/safety.rs`,
   `codegen_attrs.rs`, `link_attrs.rs`, `symbol_export.rs`), including `export_name`
   precedence over `no_mangle`, non-export of bare `link_section`, and the cross-edition
   macro-span boundary (`ce5_cross_edition_macro_bypass`).

Every `def` in this module is declared `noncomputable def` so the compiler emits zero
`._unsafe_rec` auxiliary constants, and no `deriving` clauses are used on inductive types
with `List`/`Option` fields.
-/

namespace StaticElfSectionPlacementAndUnsafeAttrsSoundness

/-! ## 1. Constructive Arithmetic, Option, and Association-List Helpers -/

noncomputable def natBeq (a b : Nat) : Bool := Nat.beq a b

theorem natBeq_refl (n : Nat) : natBeq n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem natBeq_eq {a b : Nat} (h : natBeq a b = true) : a = b :=
  Nat.eq_of_beq_eq_true h

theorem natBeq_false_of_ne {a b : Nat} (h : a ≠ b) : natBeq a b = false := by
  cases hbeq : natBeq a b
  · rfl
  · exact False.elim (h (natBeq_eq hbeq))

noncomputable def natListAllZero (xs : List Nat) : Bool :=
  xs.foldr (fun x acc => if natBeq x 0 then acc else false) true

theorem natListAllZero_nil : natListAllZero [] = true := rfl

theorem natListAllZero_cons (x : Nat) (xs : List Nat) :
    natListAllZero (x :: xs) = (if natBeq x 0 then natListAllZero xs else false) := rfl

theorem natListAllZero_true_iff (xs : List Nat) :
    natListAllZero xs = true ↔ ∀ i (h : i < xs.length), xs[i] = 0 := by
  induction xs with
  | nil =>
    constructor
    · intro _ i h
      exact False.elim (Nat.not_lt_zero i h)
    · intro _
      rfl
  | cons y ys ih =>
    constructor
    · intro h i hi
      rw [natListAllZero_cons] at h
      cases hy : natBeq y 0
      · rw [hy] at h
        cases h
      · rw [hy] at h
        have hy0 : y = 0 := natBeq_eq hy
        cases i with
        | zero => exact hy0
        | succ j =>
          have hj : j < ys.length := Nat.lt_of_succ_lt_succ hi
          exact (ih.mp h) j hj
    · intro h
      have hy0 : y = 0 := h 0 (Nat.zero_lt_succ ys.length)
      subst hy0
      rw [natListAllZero_cons]
      have hsub : natBeq 0 0 = true := rfl
      rw [hsub]
      apply ih.mpr
      intro j hj
      exact h (j + 1) (Nat.succ_lt_succ hj)

noncomputable def replicateZero (n : Nat) : List Nat :=
  Nat.repeat (fun acc => 0 :: acc) n []

theorem replicateZero_succ (n : Nat) :
    replicateZero (n + 1) = 0 :: replicateZero n := rfl

theorem replicateZero_length (n : Nat) : (replicateZero n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [replicateZero_succ, List.length_cons, ih]

theorem replicateZero_getElem (n i : Nat) (h : i < (replicateZero n).length) :
    (replicateZero n)[i] = 0 := by
  induction n generalizing i with
  | zero =>
    dsimp only [replicateZero, List.length_nil] at h
    exact False.elim (Nat.not_lt_zero i h)
  | succ k ih =>
    cases i with
    | zero => rfl
    | succ j =>
      simp only [replicateZero_succ, List.length_cons] at h
      exact ih j (Nat.lt_of_succ_lt_succ h)

theorem list_eq_replicateZero_of_allZero (xs : List Nat) (hz : natListAllZero xs = true) :
    xs = replicateZero xs.length := by
  apply List.ext_getElem
  · rw [replicateZero_length]
  · intro i h1 h2
    rw [(natListAllZero_true_iff xs).mp hz i h1]
    rw [replicateZero_getElem xs.length i h2]

noncomputable def writeAtOffset (xs : List Nat) (off val : Nat) : Option (List Nat) :=
  match xs, off with
  | [], _ => none
  | _ :: rest, 0 => some (val :: rest)
  | x :: rest, k + 1 =>
    match writeAtOffset rest k val with
    | none => none
    | some rest' => some (x :: rest')

theorem writeAtOffset_some_of_lt (xs : List Nat) (off val : Nat) (h : off < xs.length) :
    ∃ ys, writeAtOffset xs off val = some ys ∧ ys.length = xs.length := by
  induction xs generalizing off with
  | nil => exact False.elim (Nat.not_lt_zero off h)
  | cons x rest ih =>
    cases off with
    | zero => exact ⟨val :: rest, rfl, rfl⟩
    | succ k =>
      have hk : k < rest.length := Nat.lt_of_succ_lt_succ h
      obtain ⟨ys, hys, hlen⟩ := ih k hk
      refine ⟨x :: ys, ?_, ?_⟩
      · simp only [writeAtOffset, hys]
      · simp only [List.length_cons, hlen]

theorem writeAtOffset_getElem_other (xs ys : List Nat) (off val idx : Nat)
    (hw : writeAtOffset xs off val = some ys)
    (h1 : idx < xs.length) (h2 : idx < ys.length) (hne : idx ≠ off) :
    ys[idx] = xs[idx] := by
  induction xs generalizing off ys idx with
  | nil => cases hw
  | cons x rest ih =>
    cases off with
    | zero =>
      dsimp only [writeAtOffset] at hw
      injection hw with hy
      subst hy
      cases idx with
      | zero => exact False.elim (hne rfl)
      | succ j => rfl
    | succ k =>
      dsimp only [writeAtOffset] at hw
      cases hrec : writeAtOffset rest k val with
      | none => rw [hrec] at hw; cases hw
      | some rest' =>
        rw [hrec] at hw
        injection hw with hy
        subst hy
        cases idx with
        | zero => rfl
        | succ j =>
          have hj_ne : j ≠ k := fun hjk => hne (congrArg Nat.succ hjk)
          exact ih rest' k j hrec (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2) hj_ne

theorem writeAtOffset_getElem_self (xs ys : List Nat) (off val : Nat)
    (hw : writeAtOffset xs off val = some ys)
    (h2 : off < ys.length) :
    ys[off] = val := by
  induction xs generalizing off ys with
  | nil => cases hw
  | cons x rest ih =>
    cases off with
    | zero =>
      dsimp only [writeAtOffset] at hw
      injection hw with hy
      subst hy
      rfl
    | succ k =>
      dsimp only [writeAtOffset] at hw
      cases hrec : writeAtOffset rest k val with
      | none => rw [hrec] at hw; cases hw
      | some rest' =>
        rw [hrec] at hw
        injection hw with hy
        subst hy
        exact ih rest' k hrec (Nat.lt_of_succ_lt_succ h2)

noncomputable def assocLookup {α : Type} (xs : List (Nat × α)) (k : Nat) : Option α :=
  xs.foldr (fun p acc => if natBeq p.1 k then some p.2 else acc) none

noncomputable def assocUpdate {α : Type} (xs : List (Nat × α)) (k : Nat) (v : α) : List (Nat × α) :=
  xs.map (fun p => if natBeq p.1 k then (p.1, v) else p)

noncomputable def assocMap {α β : Type} (xs : List (Nat × α)) (f : Nat → α → β) : List (Nat × β) :=
  xs.map (fun p => (p.1, f p.1 p.2))

theorem assocLookup_cons_hit {α : Type} (k : Nat) (v : α) (xs : List (Nat × α)) :
    assocLookup ((k, v) :: xs) k = some v := by
  dsimp only [assocLookup, List.foldr]
  rw [natBeq_refl k]
  rfl

theorem assocLookup_cons_miss {α : Type} {k k' : Nat} (v : α) (xs : List (Nat × α))
    (hne : k' ≠ k) :
    assocLookup ((k', v) :: xs) k = assocLookup xs k := by
  dsimp only [assocLookup, List.foldr]
  rw [natBeq_false_of_ne hne]
  rfl

theorem assocLookup_update_self {α : Type} (xs : List (Nat × α)) (k : Nat) (v : α)
    {old : α} (h : assocLookup xs k = some old) :
    assocLookup (assocUpdate xs k v) k = some v := by
  induction xs with
  | nil => cases h
  | cons p ps ih =>
    dsimp only [assocUpdate, List.map, assocLookup, List.foldr] at *
    cases hp : natBeq p.1 k
    · rw [hp] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      simp only [hp, Bool.false_eq_true, ↓reduceIte]
      exact ih h
    · have hpeq : p.1 = k := natBeq_eq hp
      subst hpeq
      simp only [natBeq_refl, ↓reduceIte]

theorem assocLookup_update_other {α : Type} (xs : List (Nat × α)) (k k' : Nat) (v : α)
    (hne : k ≠ k') :
    assocLookup (assocUpdate xs k v) k' = assocLookup xs k' := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    dsimp only [assocUpdate, List.map, assocLookup, List.foldr]
    cases hp1 : natBeq p.1 k
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hp2 : natBeq p.1 k'
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih
      · simp only [↓reduceIte]
    · have hpeq : p.1 = k := natBeq_eq hp1
      subst hpeq
      simp only [↓reduceIte, natBeq_false_of_ne hne, Bool.false_eq_true]
      exact ih

theorem assocLookup_map {α β : Type} (xs : List (Nat × α)) (f : Nat → α → β) (k : Nat) :
    assocLookup (assocMap xs f) k = (assocLookup xs k).map (f k) := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    dsimp only [assocMap, List.map, assocLookup, List.foldr]
    cases hp : natBeq p.1 k
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih
    · have hpeq : p.1 = k := natBeq_eq hp
      subst hpeq
      simp only [↓reduceIte]
      rfl


/-! ## 2. Five-Category Static ELF Section Classifier & Invariants -/

/-- Rust static declaration mutability class (`intern_const_alloc_recursive`,
`compiler/rustc_const_eval/src/interpret/intern.rs:215-240`).
- `immutable`: `static X: T = ...` where `T : Freeze` (`!hasMutInterior`)
- `interiorMut`: `static X: T = ...` where `¬(T : Freeze)` (`UnsafeCell`, `Atomic*`)
- `staticMut`: `static mut X: T = ...` -/
inductive StaticMutability where
  | immutable
  | interiorMut
  | staticMut

/-- Target relocation model (`TM.getRelocationModel()`,
`llvm/lib/Target/TargetLoweringObjectFile.cpp:354-363`). -/
inductive RelocModel where
  | pic
  | staticModel

/-- ELF output section family for static data globals
(`TargetLoweringObjectFileImpl.cpp:616-631`). -/
inductive SectionKind where
  | rodata
  | dataRelRo
  | data
  | bss

/-- ELF section header `sh_type` (`TargetLoweringObjectFileImpl.cpp:524-527`). -/
inductive ElfProgBits where
  | progbits
  | nobits

/-- ELF section header permission flags (`SHF_ALLOC` vs `SHF_WRITE | SHF_ALLOC`,
`TargetLoweringObjectFileImpl.cpp:530-561`). -/
inductive ElfFlags where
  | flagsA
  | flagsWA

/-- Combined classification output for a static item in a relocatable `.o` file. -/
structure PlacementTarget where
  secKind : SectionKind
  progBits : ElfProgBits
  flags : ElfFlags
  hasRela : Bool

noncomputable def sectionKindEq (a b : SectionKind) : Bool :=
  match a, b with
  | .rodata, .rodata => true
  | .dataRelRo, .dataRelRo => true
  | .data, .data => true
  | .bss, .bss => true
  | _, _ => false

theorem sectionKindEq_iff (a b : SectionKind) : sectionKindEq a b = true ↔ a = b := by
  cases a <;> cases b <;> constructor <;> intro h <;> first | rfl | cases h

noncomputable def elfFlagsEq (a b : ElfFlags) : Bool :=
  match a, b with
  | .flagsA, .flagsA => true
  | .flagsWA, .flagsWA => true
  | _, _ => false

theorem elfFlagsEq_iff (a b : ElfFlags) : elfFlagsEq a b = true ↔ a = b := by
  cases a <;> cases b <;> constructor <;> intro h <;> first | rfl | cases h

/-- Whether Rust's `intern_const_alloc_recursive` marks the root allocation
mutable (`Mutability::Mut` -> `!isConstant()` in LLVM). -/
noncomputable def hasInteriorOrMut : StaticMutability → Bool
  | .immutable => false
  | .interiorMut => true
  | .staticMut => true

/-- Exact 5-category static ELF section classifier parameterized by
`(relocModel, mutOrInt, hasReloc, isZero)` matching:
- `consts.rs:537-539`: `set_global_constant(g, true)` iff `alloc.mutability.is_not()` (`!mutOrInt`)
- `TargetLoweringObjectFile.cpp:82-99` (`isSuitableForBSS`): returns `false` when `GV->isConstant()` or `!isNullOrUndef(C)` (i.e., `hasReloc = true` or `isZero = false`)
- `TargetLoweringObjectFile.cpp:283-367` (`getKindForGlobal`):
  1. `(!mutOrInt, false, false)` -> `.rodata` (`PROGBITS`, `A`, `hasRela = false`)
  2. `(!mutOrInt, false, true)`  -> `.rodata` (`PROGBITS`, `A`, `hasRela = false`) -- NOT `.bss`!
  3. `(!mutOrInt, true,  _)`     -> `.pic`: `.data.rel.ro` (`PROGBITS`, `WA`, `hasRela = true`)
                                 -> `.staticModel`: `.rodata` (`PROGBITS`, `A`, `hasRela = true`)
  4. `(true, true, _)`           -> `.data` (`PROGBITS`, `WA`, `hasRela = true`) -- NEVER `.data.rel.ro`!
  5. `(true, false, false)`      -> `.data` (`PROGBITS`, `WA`, `hasRela = false`)
  6. `(true, false, true)`       -> `.bss` (`NOBITS`, `WA`, `hasRela = false`). -/
noncomputable def classifyStaticSection
    (rm : RelocModel) (mutOrInt hasReloc isZero : Bool) : PlacementTarget :=
  if mutOrInt then
    if hasReloc then
      { secKind := .data, progBits := .progbits, flags := .flagsWA, hasRela := true }
    else if isZero then
      { secKind := .bss, progBits := .nobits, flags := .flagsWA, hasRela := false }
    else
      { secKind := .data, progBits := .progbits, flags := .flagsWA, hasRela := false }
  else
    if hasReloc then
      match rm with
      | .pic =>
        { secKind := .dataRelRo, progBits := .progbits, flags := .flagsWA, hasRela := true }
      | .staticModel =>
        { secKind := .rodata, progBits := .progbits, flags := .flagsA, hasRela := true }
    else
      { secKind := .rodata, progBits := .progbits, flags := .flagsA, hasRela := false }

theorem classify_immutable_never_bss (rm : RelocModel) (hasReloc isZero : Bool) :
    (classifyStaticSection rm false hasReloc isZero).secKind ≠ .bss ∧
    (classifyStaticSection rm false hasReloc isZero).progBits = .progbits := by
  cases rm <;> cases hasReloc <;> cases isZero <;>
    · refine ⟨?_, rfl⟩
      intro h
      cases h

theorem classify_immutable_zero_lands_in_rodata (rm : RelocModel) :
    classifyStaticSection rm false false true =
      { secKind := .rodata, progBits := .progbits, flags := .flagsA, hasRela := false } := by
  rfl

theorem classify_pic_immut_reloc_is_dataRelRo (isZero : Bool) :
    classifyStaticSection .pic false true isZero =
      { secKind := .dataRelRo, progBits := .progbits, flags := .flagsWA, hasRela := true } := by
  rfl

theorem classify_static_immut_reloc_is_rodata (isZero : Bool) :
    classifyStaticSection .staticModel false true isZero =
      { secKind := .rodata, progBits := .progbits, flags := .flagsA, hasRela := true } := by
  rfl

theorem classify_interior_mut_always_writable (rm : RelocModel) (hasReloc isZero : Bool) :
    (classifyStaticSection rm true hasReloc isZero).flags = .flagsWA ∧
    (classifyStaticSection rm true hasReloc isZero).secKind ≠ .rodata ∧
    (classifyStaticSection rm true hasReloc isZero).secKind ≠ .dataRelRo := by
  cases hasReloc <;> cases isZero <;>
    · refine ⟨rfl, ?_, ?_⟩ <;> intro h <;> cases h

theorem classify_interior_mut_reloc_is_data (rm : RelocModel) (isZero : Bool) :
    classifyStaticSection rm true true isZero =
      { secKind := .data, progBits := .progbits, flags := .flagsWA, hasRela := true } := by
  rfl

theorem classify_interior_mut_zero_is_bss (rm : RelocModel) :
    classifyStaticSection rm true false true =
      { secKind := .bss, progBits := .nobits, flags := .flagsWA, hasRela := false } := by
  rfl

theorem classify_bss_iff (rm : RelocModel) (mutOrInt hasReloc isZero : Bool) :
    (classifyStaticSection rm mutOrInt hasReloc isZero).secKind = .bss ↔
      (mutOrInt = true ∧ hasReloc = false ∧ isZero = true) := by
  cases rm <;> cases mutOrInt <;> cases hasReloc <;> cases isZero <;>
    · constructor
      · intro h
        first | exact ⟨rfl, rfl, rfl⟩ | cases h
      · intro ⟨h1, h2, h3⟩
        cases h1 <;> cases h2 <;> cases h3 <;> rfl

theorem classify_nobits_iff_bss (rm : RelocModel) (mutOrInt hasReloc isZero : Bool) :
    (classifyStaticSection rm mutOrInt hasReloc isZero).progBits = .nobits ↔
      (classifyStaticSection rm mutOrInt hasReloc isZero).secKind = .bss := by
  cases rm <;> cases mutOrInt <;> cases hasReloc <;> cases isZero <;>
    · constructor <;> intro h <;> first | rfl | cases h

theorem classify_rela_iff_hasReloc (rm : RelocModel) (mutOrInt hasReloc isZero : Bool) :
    (classifyStaticSection rm mutOrInt hasReloc isZero).hasRela = hasReloc := by
  cases rm <;> cases mutOrInt <;> cases hasReloc <;> cases isZero <;> rfl


/-! ## 3. Two-Phase Loader, `PT_GNU_RELRO` Memory Model, and Soundness Theorems -/

/-- Runtime virtual memory protection of a loaded static's page. -/
inductive PagePerm where
  | ro
  | rw

noncomputable def permOfFlags : ElfFlags → PagePerm
  | .flagsA => .ro
  | .flagsWA => .rw

/-- Relocation entry targeting byte offset `offset` inside a static object,
writing `patchVal`. -/
structure RelocSpec where
  offset : Nat
  patchVal : Nat

/-- Static declaration annotated with its Rust mutability, raw image bytes, and relocations. -/
structure StaticDecl where
  symId : Nat
  mutability : StaticMutability
  initBytes : List Nat
  relocs : List RelocSpec

noncomputable def StaticDecl.hasReloc (d : StaticDecl) : Bool :=
  match d.relocs with
  | [] => false
  | _ => true

noncomputable def StaticDecl.isAllZero (d : StaticDecl) : Bool :=
  natListAllZero d.initBytes

noncomputable def StaticDecl.target (rm : RelocModel) (d : StaticDecl) : PlacementTarget :=
  classifyStaticSection rm (hasInteriorOrMut d.mutability) d.hasReloc d.isAllZero

/-- Runtime state of a loaded static symbol in memory. -/
structure LoadedSym where
  mutability : StaticMutability
  sectionKind : SectionKind
  progBits : ElfProgBits
  loadedBytes : List Nat
  perm : PagePerm

/-- Machine-level trap outcomes for dynamic relocation and runtime execution. -/
inductive TrapKind where
  | sigsegv
  | relocTrap
  | oobFault
  | missingSym

inductive StepResult (α : Type) where
  | ok (val : α)
  | fault (kind : TrapKind)

/-- Emitted ELF section + relocation image produced from a `StaticDecl` under `PlacementTarget`. -/
structure EmittedSym where
  decl : StaticDecl
  placed : PlacementTarget

noncomputable def emitWithClassifier (rm : RelocModel) (d : StaticDecl) : EmittedSym :=
  { decl := d, placed := d.target rm }

/-- Phase 1 (OS ELF loader): maps `PROGBITS` from `initBytes` and `NOBITS` as
`replicateZero initBytes.length`, setting initial page permission from `placed.flags`. -/
noncomputable def loadEmittedSym (e : EmittedSym) : LoadedSym :=
  let bytes :=
    match e.placed.progBits with
    | .progbits => e.decl.initBytes
    | .nobits => replicateZero e.decl.initBytes.length
  { mutability := e.decl.mutability
  , sectionKind := e.placed.secKind
  , progBits := e.placed.progBits
  , loadedBytes := bytes
  , perm := permOfFlags e.placed.flags }

structure MachineState where
  syms : List (Nat × LoadedSym)
  relroFrozen : Bool

noncomputable def loadProgram (es : List EmittedSym) : MachineState :=
  { syms := es.map (fun e => (e.decl.symId, loadEmittedSym e))
  , relroFrozen := false }

/-- Phase 2 (Dynamic Linker `ld.so`): apply one relocation patch to `symId` at `rel.offset`.
Requires `sym.perm = .rw` and `rel.offset < sym.loadedBytes.length`; otherwise traps! -/
noncomputable def applyOneReloc (st : MachineState) (symId : Nat) (rel : RelocSpec) :
    StepResult MachineState :=
  match assocLookup st.syms symId with
  | none => .fault .missingSym
  | some sym =>
    match sym.perm with
    | .ro => .fault .relocTrap
    | .rw =>
      match writeAtOffset sym.loadedBytes rel.offset rel.patchVal with
      | none => .fault .oobFault
      | some bytes' =>
        let sym' := { sym with loadedBytes := bytes' }
        .ok { st with syms := assocUpdate st.syms symId sym' }

noncomputable def applySymRelocs (st : MachineState) (symId : Nat) (rels : List RelocSpec) :
    StepResult MachineState :=
  match rels with
  | [] => .ok st
  | r :: rs =>
    match applyOneReloc st symId r with
    | .fault k => .fault k
    | .ok st' => applySymRelocs st' symId rs

noncomputable def applyAllRelocs (st : MachineState) (es : List EmittedSym) :
    StepResult MachineState :=
  match es with
  | [] => .ok st
  | e :: rest =>
    match applySymRelocs st e.decl.symId e.decl.relocs with
    | .fault k => .fault k
    | .ok st' => applyAllRelocs st' rest

/-- Phase 2b (`PT_GNU_RELRO` `mprotect(..., PROT_READ)`): freezes `.dataRelRo` pages
to `.ro` before transferring control to `main`, leaving `.rodata` at `.ro` and
`.data`/`.bss` at `.rw`. -/
noncomputable def applyRelroProtect (st : MachineState) : MachineState :=
  let freezeSym := fun (_ : Nat) (s : LoadedSym) =>
    match s.sectionKind with
    | .dataRelRo => { s with perm := .ro }
    | _ => s
  { syms := assocMap st.syms freezeSym, relroFrozen := true }

/-- Phase 3 (User Program Operations after RELRO freeze). -/
inductive RuntimeOp where
  | read (symId offset : Nat)
  | write (symId offset val : Nat)

noncomputable def execRuntimeOp (st : MachineState) (op : RuntimeOp) :
    StepResult (MachineState × Option Nat) :=
  match op with
  | .read symId off =>
    match assocLookup st.syms symId with
    | none => .fault .missingSym
    | some sym =>
      match sym.loadedBytes[off]? with
      | none => .fault .oobFault
      | some v => .ok (st, some v)
  | .write symId off val =>
    match assocLookup st.syms symId with
    | none => .fault .missingSym
    | some sym =>
      match sym.perm with
      | .ro => .fault .sigsegv
      | .rw =>
        match writeAtOffset sym.loadedBytes off val with
        | none => .fault .oobFault
        | some bytes' =>
          let sym' := { sym with loadedBytes := bytes' }
          .ok ({ st with syms := assocUpdate st.syms symId sym' }, none)

noncomputable def execRuntimeTrace (st : MachineState) (ops : List RuntimeOp) :
    StepResult MachineState :=
  match ops with
  | [] => .ok st
  | op :: rest =>
    match execRuntimeOp st op with
    | .fault k => .fault k
    | .ok (st', _) => execRuntimeTrace st' rest

/-- Well-formed relocation specification: every relocation offset is in-bounds of `d.initBytes`. -/
noncomputable def RelocsInBounds (d : StaticDecl) : Prop :=
  ∀ r, r ∈ d.relocs → r.offset < d.initBytes.length

/-- Pairwise distinct symbol IDs in an object/program module. -/
noncomputable def DistinctSymIds : List EmittedSym → Prop
  | [] => True
  | e :: es => (∀ e', e' ∈ es → e'.decl.symId ≠ e.decl.symId) ∧ DistinctSymIds es

theorem assocLookup_loadProgram_self (e : EmittedSym) (es : List EmittedSym) :
    assocLookup (loadProgram (e :: es)).syms e.decl.symId = some (loadEmittedSym e) := by
  dsimp only [loadProgram, List.map]
  exact assocLookup_cons_hit e.decl.symId (loadEmittedSym e) _

theorem assocLookup_loadProgram_none_of_not_mem (es : List EmittedSym) (k : Nat)
    (hnot : ∀ e, e ∈ es → e.decl.symId ≠ k) :
    assocLookup (loadProgram es).syms k = none := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
    dsimp only [loadProgram, List.map]
    rw [assocLookup_cons_miss (loadEmittedSym e) _ (hnot e (List.mem_cons_self))]
    exact ih (fun e' he' => hnot e' (List.mem_cons_of_mem e he'))

theorem assocLookup_loadProgram_mem (es : List EmittedSym) (e : EmittedSym)
    (hdist : DistinctSymIds es) (hmem : e ∈ es) :
    assocLookup (loadProgram es).syms e.decl.symId = some (loadEmittedSym e) := by
  induction es with
  | nil => cases hmem
  | cons x xs ih =>
    cases hmem with
    | head => exact assocLookup_loadProgram_self _ xs
    | tail _ hmem_xs =>
      dsimp only [DistinctSymIds] at hdist
      have hne : x.decl.symId ≠ e.decl.symId := Ne.symm (hdist.1 e hmem_xs)
      dsimp only [loadProgram, List.map]
      rw [assocLookup_cons_miss (loadEmittedSym x) _ hne]
      exact ih hdist.2 hmem_xs

/-- Theorem 1 (Initial Image Fidelity): Under `classifyStaticSection`, `loadEmittedSym`
always reconstructs `d.initBytes` byte-for-byte (`.bss` is chosen only when `isAllZero = true`). -/
theorem load_preserves_init_bytes (rm : RelocModel) (d : StaticDecl) :
    (loadEmittedSym (emitWithClassifier rm d)).loadedBytes = d.initBytes := by
  dsimp only [loadEmittedSym, emitWithClassifier, StaticDecl.target, classifyStaticSection]
  cases hmut : hasInteriorOrMut d.mutability
  · cases hrel : d.hasReloc
    · rfl
    · cases rm <;> rfl
  · cases hrel : d.hasReloc
    · cases hz : d.isAllZero
      · rfl
      · exact Eq.symm (list_eq_replicateZero_of_allZero d.initBytes hz)
    · rfl

/-- Theorem 2 (Pre-RELRO Dynamic Relocation Safety — PIC): Under PIC relocation model,
every static that has relocations (`d.hasReloc = true`) is placed in a `WA` (`perm = .rw`)
section (`.dataRelRo` if immutable, `.data` if interior-mutable/static-mut) at load time. -/
theorem pic_reloc_sym_is_rw_at_load (d : StaticDecl) (hrel : d.hasReloc = true) :
    (loadEmittedSym (emitWithClassifier .pic d)).perm = .rw := by
  dsimp only [loadEmittedSym, emitWithClassifier, StaticDecl.target, classifyStaticSection]
  rw [hrel]
  cases hasInteriorOrMut d.mutability <;> rfl

/-- Helper: applying a list of in-bounds relocations to a single `LoadedSym` whose
`perm = .rw` always succeeds, preserves `perm`, `mutability`, `sectionKind`, `progBits`,
`loadedBytes.length`, and leaves all other symbols in `st.syms` untouched. -/
theorem applySymRelocs_rw_succeeds (st : MachineState) (sid : Nat) (sym : LoadedSym)
    (rels : List RelocSpec)
    (hlookup : assocLookup st.syms sid = some sym)
    (hperm : sym.perm = .rw)
    (hbounds : ∀ r, r ∈ rels → r.offset < sym.loadedBytes.length) :
    ∃ st' sym',
      applySymRelocs st sid rels = .ok st' ∧
      assocLookup st'.syms sid = some sym' ∧
      sym'.perm = .rw ∧
      sym'.mutability = sym.mutability ∧
      sym'.sectionKind = sym.sectionKind ∧
      sym'.progBits = sym.progBits ∧
      sym'.loadedBytes.length = sym.loadedBytes.length ∧
      (∀ other, other ≠ sid → assocLookup st'.syms other = assocLookup st.syms other) := by
  induction rels generalizing st sym with
  | nil =>
    exact ⟨st, sym, rfl, hlookup, hperm, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons r rs ih =>
    have hr_bound : r.offset < sym.loadedBytes.length := hbounds r (List.mem_cons_self)
    obtain ⟨bytes', hwrite, hlen⟩ := writeAtOffset_some_of_lt sym.loadedBytes r.offset r.patchVal hr_bound
    let sym1 : LoadedSym := { sym with loadedBytes := bytes', perm := .rw }
    let st1 : MachineState := { st with syms := assocUpdate st.syms sid sym1 }
    have hstep : applyOneReloc st sid r = .ok st1 := by
      dsimp only [applyOneReloc, st1, sym1]
      rw [hlookup]
      dsimp only
      rw [hperm]
      dsimp only
      rw [hwrite]
    have hlookup1 : assocLookup st1.syms sid = some sym1 :=
      assocLookup_update_self st.syms sid sym1 hlookup
    have hbounds1 : ∀ r', r' ∈ rs → r'.offset < sym1.loadedBytes.length := by
      intro r' hr'
      rw [hlen]
      exact hbounds r' (List.mem_cons_of_mem r hr')
    obtain ⟨st2, sym2, happly, hlook2, hperm2, hmut2, hsec2, hpb2, hlen2, hother2⟩ :=
      ih st1 sym1 hlookup1 rfl hbounds1
    refine ⟨st2, sym2, ?_, hlook2, hperm2, hmut2, hsec2, hpb2, ?_, ?_⟩
    · dsimp only [applySymRelocs]
      rw [hstep]
      exact happly
    · rw [hlen2, hlen]
    · intro other hne
      rw [hother2 other hne]
      exact assocLookup_update_other st.syms sid other sym1 (fun h => hne (Eq.symm h))

/-- Invariant satisfied by a `MachineState` produced by loading classifier-emitted PIC statics
and applying any prefix of dynamic relocations. -/
noncomputable def PicPreRelroInv (st : MachineState) (es : List EmittedSym) : Prop :=
  ∀ e, e ∈ es → ∃ sym,
    assocLookup st.syms e.decl.symId = some sym ∧
    sym.mutability = e.decl.mutability ∧
    sym.sectionKind = e.placed.secKind ∧
    sym.progBits = e.placed.progBits ∧
    sym.loadedBytes.length = e.decl.initBytes.length ∧
    sym.perm = permOfFlags e.placed.flags

theorem picPreRelroInv_loadProgram (es : List EmittedSym) (hdist : DistinctSymIds es)
    (hpic : ∀ e, e ∈ es → e = emitWithClassifier .pic e.decl) :
    PicPreRelroInv (loadProgram es) es := by
  intro e hmem
  refine ⟨loadEmittedSym e, assocLookup_loadProgram_mem es e hdist hmem, rfl, rfl, rfl, ?_, rfl⟩
  have heq := hpic e hmem
  rw [heq]
  exact congrArg List.length (load_preserves_init_bytes .pic e.decl)

/-- Theorem 3 (Complete Pre-RELRO Dynamic Relocation Phase Soundness under PIC):
Given distinct symbol IDs and in-bounds relocations, `applyAllRelocs` succeeds across
the entire program with zero `relocTrap` / `oobFault` and preserves every symbol's
section classification, mutability, size, and initial `PagePerm`. -/
theorem pic_applyAllRelocs_succeeds (todo allEs : List EmittedSym) (st : MachineState)
    (hsub : ∀ e, e ∈ todo → e ∈ allEs)
    (hinv : PicPreRelroInv st allEs)
    (hpic : ∀ e, e ∈ todo → e = emitWithClassifier .pic e.decl)
    (hbounds : ∀ e, e ∈ todo → RelocsInBounds e.decl) :
    ∃ st',
      applyAllRelocs st todo = .ok st' ∧
      PicPreRelroInv st' allEs := by
  induction todo generalizing st with
  | nil => exact ⟨st, rfl, hinv⟩
  | cons e rest ih =>
    have he_all : e ∈ allEs := hsub e List.mem_cons_self
    obtain ⟨sym, hlook, hmut, hsec, hpb, hlen, hperm⟩ := hinv e he_all
    have hpic_e := hpic e List.mem_cons_self
    cases hrels : e.decl.relocs with
    | nil =>
      have hnoop : applySymRelocs st e.decl.symId e.decl.relocs = .ok st := by
        rw [hrels]; rfl
      have hall_rest :
          applyAllRelocs st (e :: rest) = applyAllRelocs st rest := by
        dsimp only [applyAllRelocs]; rw [hnoop]
      rw [hall_rest]
      exact ih st
        (fun x hx => hsub x (List.mem_cons_of_mem e hx))
        hinv
        (fun x hx => hpic x (List.mem_cons_of_mem e hx))
        (fun x hx => hbounds x (List.mem_cons_of_mem e hx))
    | cons r rs =>
      have hhasrel : e.decl.hasReloc = true := by
        dsimp only [StaticDecl.hasReloc]; rw [hrels]
      have hplaced_flags : e.placed.flags = .flagsWA := by
        rw [hpic_e]
        dsimp only [emitWithClassifier, StaticDecl.target, classifyStaticSection]
        rw [hhasrel]
        cases hasInteriorOrMut e.decl.mutability <;> rfl
      have hsym_rw : sym.perm = .rw := by
        rw [hperm, hplaced_flags]; rfl
      have hsym_bounds : ∀ r', r' ∈ e.decl.relocs → r'.offset < sym.loadedBytes.length := by
        intro r' hr'
        rw [hlen]
        exact hbounds e List.mem_cons_self r' hr'
      obtain ⟨st1, sym1, happ1, hlook1, hperm1, hmut1, hsec1, hpb1, hlen1, hother1⟩ :=
        applySymRelocs_rw_succeeds st e.decl.symId sym e.decl.relocs hlook hsym_rw hsym_bounds
      have hinv1 : PicPreRelroInv st1 allEs := by
        intro x hx
        by_cases hsid : x.decl.symId = e.decl.symId
        · obtain ⟨sx, hlookx, hmutx, hsecx, hpbx, hlenx, hpermx⟩ := hinv x hx
          rw [hsid] at hlookx
          rw [hlook] at hlookx
          injection hlookx with hsx
          subst hsx
          refine ⟨sym1, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hsid]; exact hlook1
          · rw [hmut1]; exact hmutx
          · rw [hsec1]; exact hsecx
          · rw [hpb1]; exact hpbx
          · rw [hlen1]; exact hlenx
          · rw [hperm1, ← hsym_rw]; exact hpermx
        · obtain ⟨sx, hlookx, hmutx, hsecx, hpbx, hlenx, hpermx⟩ := hinv x hx
          refine ⟨sx, ?_, hmutx, hsecx, hpbx, hlenx, hpermx⟩
          rw [hother1 x.decl.symId hsid]
          exact hlookx
      obtain ⟨st2, happ2, hinv2⟩ := ih st1
        (fun x hx => hsub x (List.mem_cons_of_mem e hx))
        hinv1
        (fun x hx => hpic x (List.mem_cons_of_mem e hx))
        (fun x hx => hbounds x (List.mem_cons_of_mem e hx))
      refine ⟨st2, ?_, hinv2⟩
      dsimp only [applyAllRelocs]
      rw [happ1]
      exact happ2

/-- Post-RELRO Hardware Memory-Protection Invariant:
1. Every `.immutable` static (`.rodata` or `.dataRelRo`) has **`perm = .ro`**;
2. Every `.interiorMut` or `.staticMut` static (`.data` or `.bss`) has **`perm = .rw`**. -/
noncomputable def PostRelroMemSafeInv (st : MachineState) (es : List EmittedSym) : Prop :=
  ∀ e, e ∈ es → ∃ sym,
    assocLookup st.syms e.decl.symId = some sym ∧
    sym.mutability = e.decl.mutability ∧
    sym.sectionKind = e.placed.secKind ∧
    sym.loadedBytes.length = e.decl.initBytes.length ∧
    (hasInteriorOrMut e.decl.mutability = false → sym.perm = .ro) ∧
    (hasInteriorOrMut e.decl.mutability = true → sym.perm = .rw)

theorem applyRelroProtect_establishes_postRelroMemSafeInv
    (st : MachineState) (es : List EmittedSym)
    (hinv : PicPreRelroInv st es)
    (hpic : ∀ e, e ∈ es → e = emitWithClassifier .pic e.decl) :
    PostRelroMemSafeInv (applyRelroProtect st) es := by
  intro e hmem
  obtain ⟨sym, hlook, hmut, hsec, _hpb, hlen, hperm⟩ := hinv e hmem
  dsimp only [applyRelroProtect]
  have hmap := assocLookup_map st.syms
    (fun (_ : Nat) (s : LoadedSym) =>
      match s.sectionKind with | .dataRelRo => { s with perm := .ro } | _ => s)
    e.decl.symId
  rw [hlook] at hmap
  dsimp only [Option.map] at hmap
  have heq := hpic e hmem
  cases hmut_b : hasInteriorOrMut e.decl.mutability
  · -- Immutable case: either .rodata (perm already .ro) or .dataRelRo (frozen to .ro)
    have hsec_opts : sym.sectionKind = .rodata ∨ sym.sectionKind = .dataRelRo := by
      rw [hsec, heq]
      dsimp only [emitWithClassifier, StaticDecl.target, classifyStaticSection]
      rw [hmut_b]
      cases e.decl.hasReloc
      · exact Or.inl rfl
      · exact Or.inr rfl
    cases hsec_opts with
    | inl hro =>
      have hflags : e.placed.flags = .flagsA := by
        have hsec' := hsec
        rw [heq] at hsec'
        dsimp only [emitWithClassifier, StaticDecl.target, classifyStaticSection] at hsec'
        rw [hmut_b] at hsec'
        cases hrel : e.decl.hasReloc
        · rw [heq]; dsimp only [emitWithClassifier, StaticDecl.target, classifyStaticSection]; rw [hmut_b, hrel]; rfl
        · rw [hrel] at hsec'; rw [hsec'] at hro; cases hro
      have hsym_ro : sym.perm = .ro := by rw [hperm, hflags]; rfl
      refine ⟨sym, ?_, hmut, hsec, hlen, (fun _ => hsym_ro), (fun hc => by cases hc)⟩
      rw [hmap, hro]
    | inr hdr =>
      refine ⟨{ sym with perm := .ro }, ?_, hmut, hsec, hlen, (fun _ => rfl), (fun hc => by cases hc)⟩
      rw [hmap, hdr]
  · -- Mutable / InteriorMut case: section is .data or .bss, perm stays .rw
    have hflags : e.placed.flags = .flagsWA := by
      rw [heq]
      dsimp only [emitWithClassifier, StaticDecl.target, classifyStaticSection]
      rw [hmut_b]
      cases e.decl.hasReloc <;> cases e.decl.isAllZero <;> rfl
    have hsym_rw : sym.perm = .rw := by rw [hperm, hflags]; rfl
    have hnot_dr : sym.sectionKind ≠ .dataRelRo := by
      rw [hsec, heq]
      dsimp only [emitWithClassifier, StaticDecl.target, classifyStaticSection]
      rw [hmut_b]
      cases e.decl.hasReloc <;> cases e.decl.isAllZero <;> exact (fun hc => by cases hc)
    cases hsk : sym.sectionKind with
    | dataRelRo => exact False.elim (hnot_dr hsk)
    | rodata =>
      refine ⟨sym, ?_, hmut, hsec, hlen, (fun hc => by cases hc), (fun _ => hsym_rw)⟩
      rw [hmap, hsk]
    | data =>
      refine ⟨sym, ?_, hmut, hsec, hlen, (fun hc => by cases hc), (fun _ => hsym_rw)⟩
      rw [hmap, hsk]
    | bss =>
      refine ⟨sym, ?_, hmut, hsec, hlen, (fun hc => by cases hc), (fun _ => hsym_rw)⟩
      rw [hmap, hsk]

/-- A runtime operation is well-typed under Rust's static rules if:
- any `read` targets a declared symbol at an in-bounds offset, and
- any `write` targets a declared symbol with interior mutability or `static mut`
  (`hasInteriorOrMut = true`) at an in-bounds offset. -/
noncomputable def WellTypedRuntimeOp (es : List EmittedSym) : RuntimeOp → Prop
  | .read sid off => ∃ e, e ∈ es ∧ e.decl.symId = sid ∧ off < e.decl.initBytes.length
  | .write sid off _ =>
    ∃ e, e ∈ es ∧ e.decl.symId = sid ∧
      hasInteriorOrMut e.decl.mutability = true ∧ off < e.decl.initBytes.length

/-- Theorem 4 (Runtime Write Safety & Immutable Data Preservation Post-RELRO):
Across any trace of `WellTypedRuntimeOp` operations starting from a `PostRelroMemSafeInv`
state:
1. Execution succeeds with zero `SIGSEGV` and zero faults (`execRuntimeTrace = .ok st'`);
2. `PostRelroMemSafeInv st' es` holds inductively;
3. Every frozen immutable static (`.rodata` and `.data.rel.ro`) retains bit-identical
   `loadedBytes` across the entire runtime execution trace! -/
theorem wellTypedTrace_safe_and_preserves_immutable
    (st : MachineState) (es : List EmittedSym) (ops : List RuntimeOp)
    (hinv : PostRelroMemSafeInv st es)
    (hwt : ∀ op, op ∈ ops → WellTypedRuntimeOp es op) :
    ∃ st',
      execRuntimeTrace st ops = .ok st' ∧
      PostRelroMemSafeInv st' es ∧
      (∀ e, e ∈ es → hasInteriorOrMut e.decl.mutability = false →
        ∀ s0 s1,
          assocLookup st.syms e.decl.symId = some s0 →
          assocLookup st'.syms e.decl.symId = some s1 →
          s1.loadedBytes = s0.loadedBytes) := by
  induction ops generalizing st with
  | nil =>
    refine ⟨st, rfl, hinv, fun _ _ _ s0 s1 h0 h1 => ?_⟩
    rw [h0] at h1; injection h1 with heq; rw [heq]
  | cons op rest ih =>
    have hop_wt : WellTypedRuntimeOp es op := hwt op List.mem_cons_self
    cases op with
    | read sid off =>
      obtain ⟨e, he_mem, he_id, hoff⟩ := hop_wt
      obtain ⟨sym, hlook, _hmut, _hsec, hlen, _hro, _hrw⟩ := hinv e he_mem
      rw [he_id] at hlook
      have hoff_sym : off < sym.loadedBytes.length := by rw [hlen]; exact hoff
      have hv : sym.loadedBytes[off]? = some sym.loadedBytes[off] :=
        List.getElem?_eq_some_iff.mpr ⟨hoff_sym, rfl⟩
      have hstep : execRuntimeOp st (.read sid off) = .ok (st, some sym.loadedBytes[off]) := by
        dsimp only [execRuntimeOp]
        rw [hlook]
        dsimp only
        rw [hv]
      obtain ⟨st', hexec, hinv', hpres⟩ :=
        ih st hinv (fun o ho => hwt o (List.mem_cons_of_mem _ ho))
      refine ⟨st', ?_, hinv', hpres⟩
      dsimp only [execRuntimeTrace]
      rw [hstep]
      exact hexec
    | write sid off val =>
      obtain ⟨e, he_mem, he_id, he_mut, hoff⟩ := hop_wt
      obtain ⟨sym, hlook, hmut, hsec, hlen, hro, hrw⟩ := hinv e he_mem
      have hsym_rw : sym.perm = .rw := hrw he_mut
      have hoff_sym : off < sym.loadedBytes.length := by rw [hlen]; exact hoff
      obtain ⟨bytes', hw_bytes, hlen'⟩ := writeAtOffset_some_of_lt sym.loadedBytes off val hoff_sym
      let sym1 : LoadedSym := { sym with loadedBytes := bytes', perm := .rw }
      let st1 : MachineState := { st with syms := assocUpdate st.syms sid sym1 }
      have hstep : execRuntimeOp st (.write sid off val) = .ok (st1, none) := by
        dsimp only [execRuntimeOp, st1, sym1]
        rw [← he_id, hlook]
        dsimp only
        rw [hsym_rw]
        dsimp only
        rw [hw_bytes]
      have hinv1 : PostRelroMemSafeInv st1 es := by
        intro x hx
        obtain ⟨sx, hlookx, hmutx, hsecx, hlenx, hrox, hrwx⟩ := hinv x hx
        by_cases hxid : x.decl.symId = sid
        · rw [hxid, ← he_id] at hlookx
          rw [hlook] at hlookx
          injection hlookx with hsx
          subst hsx
          refine ⟨sym1, ?_, hmutx, hsecx, ?_, ?_, ?_⟩
          · rw [hxid]
            exact assocLookup_update_self st.syms sid sym1 (by rw [← he_id]; exact hlook)
          · rw [hlen', hlenx]
          · intro hc
            exfalso
            rw [← hmutx, hmut, he_mut] at hc
            cases hc
          · intro _
            rfl
        · refine ⟨sx, ?_, hmutx, hsecx, hlenx, hrox, hrwx⟩
          rw [assocLookup_update_other st.syms sid x.decl.symId sym1 (fun h => hxid (Eq.symm h))]
          exact hlookx
      obtain ⟨st', hexec, hinv', hpres⟩ :=
        ih st1 hinv1 (fun o ho => hwt o (List.mem_cons_of_mem _ ho))
      refine ⟨st', ?_, hinv', ?_⟩
      · dsimp only [execRuntimeTrace]
        rw [hstep]
        exact hexec
      · intro x hx_mem hx_imm s0 s1 hs0 hs1
        have hx_ne : x.decl.symId ≠ sid := by
          intro hcol
          rw [← he_id] at hcol
          obtain ⟨sx, hlookx, hmutx, _⟩ := hinv x hx_mem
          rw [hcol] at hlookx
          rw [hlook] at hlookx
          injection hlookx with hsx
          subst hsx
          rw [hmutx] at hmut
          rw [← hmut, hx_imm] at he_mut
          cases he_mut
        have hs0_st1 : assocLookup st1.syms x.decl.symId = some s0 := by
          dsimp only [st1]
          rw [assocLookup_update_other st.syms sid x.decl.symId sym1 (fun h => hx_ne (Eq.symm h))]
          exact hs0
        exact hpres x hx_mem hx_imm s0 s1 hs0_st1 hs1


/-! ## 4. Misclassification Fault Counterexamples & Linker Contamination -/

/-- Counterexample 1: Placing an `UnsafeCell`/`Atomic` static into `.rodata` (`flagsA`, `ro`)
causes a well-typed runtime write to trap with `TrapKind.sigsegv`. -/
noncomputable def ce1UnsafeCellDecl : StaticDecl :=
  { symId := 1
  , mutability := .interiorMut
  , initBytes := [7, 0, 0, 0, 0, 0, 0, 0]
  , relocs := [] }

noncomputable def ce1Misclassified : EmittedSym :=
  { decl := ce1UnsafeCellDecl
  , placed := { secKind := .rodata, progBits := .progbits, flags := .flagsA, hasRela := false } }

theorem ce1_rodata_write_trap_on_unsafecell :
    let st := applyRelroProtect (loadProgram [ce1Misclassified])
    WellTypedRuntimeOp [ce1Misclassified] (.write 1 0 88) ∧
    execRuntimeOp st (.write 1 0 88) = .fault .sigsegv := by
  constructor
  · exact ⟨ce1Misclassified, List.mem_cons_self, rfl, rfl, Nat.zero_lt_succ 7⟩
  · rfl

/-- Counterexample 2: Placing an immutable static with a pointer relocation (`&A`) into
`.rodata` (`flagsA`, `ro`) under PIC causes dynamic relocation to trap with `TrapKind.relocTrap`. -/
noncomputable def ce2RelocImmDecl : StaticDecl :=
  { symId := 2
  , mutability := .immutable
  , initBytes := [0, 0, 0, 0, 0, 0, 0, 0]
  , relocs := [{ offset := 0, patchVal := 4096 }] }

noncomputable def ce2Misclassified : EmittedSym :=
  { decl := ce2RelocImmDecl
  , placed := { secKind := .rodata, progBits := .progbits, flags := .flagsA, hasRela := true } }

theorem ce2_rodata_relocation_trap_on_pic_imm_ref :
    applyAllRelocs (loadProgram [ce2Misclassified]) [ce2Misclassified] = .fault .relocTrap := by
  rfl

/-- Counterexample 3: Placing a non-zero static (`[42, ...]`) into `.bss` (`NOBITS`)
silently discards its non-zero initial byte (`loadedBytes[0] = 0 ≠ 42`). -/
noncomputable def ce3NonZeroDecl : StaticDecl :=
  { symId := 3
  , mutability := .interiorMut
  , initBytes := [42, 0, 0, 0, 0, 0, 0, 0]
  , relocs := [] }

noncomputable def ce3Misclassified : EmittedSym :=
  { decl := ce3NonZeroDecl
  , placed := { secKind := .bss, progBits := .nobits, flags := .flagsWA, hasRela := false } }

theorem ce3_bss_data_loss_on_nonzero_init :
    let loaded := loadEmittedSym ce3Misclassified
    loaded.loadedBytes[0]? = some 0 ∧
    ce3NonZeroDecl.initBytes[0]? = some 42 ∧
    loaded.loadedBytes ≠ ce3NonZeroDecl.initBytes := by
  refine ⟨rfl, rfl, fun h => by cases h⟩

/-- Counterexample 4 (`#[unsafe(link_section = ".rodata")]` cross-section ELF flag
contamination, modeling `TargetLoweringObjectFileImpl.cpp:456-496, 530-562, 822-845`
combined with ELF linker `sh_flags` OR-merging):
When an `UnsafeCell` static overrides `link_section = ".rodata"`, LLVM emits an input
`.rodata` section with `SHF_WRITE | SHF_ALLOC` (`flagsWA`). Merging input `.rodata`
sections with bitwise OR promotes the entire output `.rodata` section to `flagsWA`,
stripping read-only hardware protection from co-located immutable statics! -/
noncomputable def mergeElfFlags : ElfFlags → ElfFlags → ElfFlags
  | .flagsA, .flagsA => .flagsA
  | _, _ => .flagsWA

noncomputable def linkSectionFlagsOverride (sName : Nat) (defaultTarget : PlacementTarget) :
    ElfFlags :=
  -- Models `getELFKindForNamedSection` + `getELFSectionFlags`:
  -- `.bss` (encoded as id 1) forces `flagsWA`; custom or `.rodata` (id 0) retains `defaultTarget.flags`.
  if natBeq sName 1 then .flagsWA else defaultTarget.flags

theorem ce4_link_section_rodata_contaminates_segment :
    let immDefault := classifyStaticSection .pic false false false
    let cellDefault := classifyStaticSection .pic true false false
    let cellInRodataFlags := linkSectionFlagsOverride 0 cellDefault
    mergeElfFlags immDefault.flags cellInRodataFlags = .flagsWA ∧
    permOfFlags (mergeElfFlags immDefault.flags cellInRodataFlags) = .rw := by
  exact ⟨rfl, rfl⟩


/-! ## 5. Edition 2024 `#[unsafe(...)]` Attribute Gate & Codegen Equivalence -/

inductive Edition where
  | ed2015
  | ed2018
  | ed2021
  | ed2024

noncomputable def editionAtLeast2024 : Edition → Bool
  | .ed2024 => true
  | _ => false

/-- Built-in attributes audited in `codegen_attrs.rs`, `link_attrs.rs`, and `safety.rs`. -/
inductive BuiltinAttrKind where
  | noMangle
  | exportName (sym : Nat)
  | linkSection (secId : Nat)
  | used
  | inline

inductive AttrSafetyAnnot where
  | bare
  | unsafeWrapped

/-- Parsed attribute occurrence carrying the edition of the attribute path span
(`path_span.edition()` in `rustc_attr_parsing/src/safety.rs:37, 53`). -/
structure AttrUse where
  kind : BuiltinAttrKind
  annot : AttrSafetyAnnot
  pathSpanEdition : Edition

inductive ExpectedSafety where
  | normal
  | unsafeSince2024

noncomputable def expectedSafetyOf : BuiltinAttrKind → ExpectedSafety
  | .noMangle => .unsafeSince2024
  | .exportName _ => .unsafeSince2024
  | .linkSection _ => .unsafeSince2024
  | .used => .normal
  | .inline => .normal

inductive AttrCheckOutcome where
  | ok
  | lintUnsafeOutsideUnsafeAndUnsafeCode
  | lintUnsafeCodeOnly
  | errUnsafeAttrOutsideUnsafe
  | errInvalidAttrUnsafe

noncomputable def isAttrError : AttrCheckOutcome → Bool
  | .errUnsafeAttrOutsideUnsafe => true
  | .errInvalidAttrUnsafe => true
  | _ => false

/-- Exact state machine for `AttributeParser::check_attribute_safety`
(`rustc_attr_parsing/src/safety.rs:25-127`):
- `(Unsafe { unsafe_since: Some(Edition2024) }, Safety::Unsafe)` -> `lintUnsafeCodeOnly` (accepted unless `-D`/`-F unsafe_code`)
- `(Unsafe { unsafe_since: Some(Edition2024) }, Safety::Default)` ->
  if `pathSpanEdition >= Edition2024` then `errUnsafeAttrOutsideUnsafe`
  else `lintUnsafeOutsideUnsafeAndUnsafeCode`
- `(Normal, Safety::Unsafe)` -> `errInvalidAttrUnsafe`
- `(Normal, Safety::Default)` -> `ok`. -/
noncomputable def checkAttributeSafety (u : AttrUse) : AttrCheckOutcome :=
  match expectedSafetyOf u.kind, u.annot with
  | .unsafeSince2024, .unsafeWrapped => .lintUnsafeCodeOnly
  | .unsafeSince2024, .bare =>
    if editionAtLeast2024 u.pathSpanEdition then
      .errUnsafeAttrOutsideUnsafe
    else
      .lintUnsafeOutsideUnsafeAndUnsafeCode
  | .normal, .unsafeWrapped => .errInvalidAttrUnsafe
  | .normal, .bare => .ok

noncomputable def checkAllAttrs : List AttrUse → Bool
  | [] => true
  | u :: us => if isAttrError (checkAttributeSafety u) then false else checkAllAttrs us

/-- Codegen attribute representation (`CodegenFnAttrs`,
`rustc_codegen_ssa/src/codegen_attrs.rs:58-116`). -/
structure CodegenAttrs where
  symbolName : Option Nat
  linkSection : Option Nat
  isUsed : Bool
  isInline : Bool

noncomputable def CodegenAttrs.empty : CodegenAttrs :=
  { symbolName := none, linkSection := none, isUsed := false, isInline := false }

noncomputable def applyOneBuiltinAttr (itemIdent : Nat) (acc : CodegenAttrs) (u : AttrUse) :
    CodegenAttrs :=
  match u.kind with
  | .exportName sym => { acc with symbolName := some sym }
  | .noMangle =>
    match acc.symbolName with
    | none => { acc with symbolName := some itemIdent }
    | some _ => acc
  | .linkSection secId => { acc with linkSection := some secId }
  | .used => { acc with isUsed := true }
  | .inline => { acc with isInline := true }

noncomputable def processBuiltinAttrs (itemIdent : Nat) (attrs : List AttrUse) : CodegenAttrs :=
  attrs.foldl (applyOneBuiltinAttr itemIdent) CodegenAttrs.empty

/-- Symbol export visibility (`symbol_export_level`, `rustc_codegen_ssa/src/back/symbol_export.rs:634-660`,
and `CodegenFnAttrs::contains_extern_indicator`, `codegen_fn_attrs.rs:269-287`). -/
inductive SymbolExportLevel where
  | rust
  | cExtern

noncomputable def containsExternIndicator (ca : CodegenAttrs) : Bool :=
  match ca.symbolName with
  | some _ => true
  | none => false

noncomputable def symbolExportLevel (ca : CodegenAttrs) : SymbolExportLevel :=
  if containsExternIndicator ca then .cExtern else .rust

/-- Theorem 5 (Edition 2024 Unsafe Attribute Gate Soundness):
Whenever an attribute with `ExpectedSafety.unsafeSince2024` (`no_mangle`, `export_name`,
`link_section`) has `pathSpanEdition = .ed2024` and passes `checkAttributeSafety` without
hard error, it MUST carry an explicit `AttrSafetyAnnot.unsafeWrapped` witness. -/
theorem edition2024_gate_requires_unsafe_witness (u : AttrUse)
    (hspec : expectedSafetyOf u.kind = .unsafeSince2024)
    (hed : u.pathSpanEdition = .ed2024)
    (hok : isAttrError (checkAttributeSafety u) = false) :
    u.annot = .unsafeWrapped := by
  cases han : u.annot with
  | unsafeWrapped => rfl
  | bare =>
    exfalso
    dsimp only [checkAttributeSafety] at hok
    rw [hspec, han, hed] at hok
    cases hok

/-- Theorem 6 (Extraneous `#[unsafe(...)]` Rejection on Normal Attributes):
Wrapping a normal attribute (`used`, `inline`) in `#[unsafe(...)]` is rejected with
`errInvalidAttrUnsafe` in every edition. -/
theorem unsafe_wrapper_rejected_on_normal_attrs (u : AttrUse)
    (hspec : expectedSafetyOf u.kind = .normal)
    (hwrap : u.annot = .unsafeWrapped) :
    checkAttributeSafety u = .errInvalidAttrUnsafe ∧
    isAttrError (checkAttributeSafety u) = true := by
  dsimp only [checkAttributeSafety, isAttrError]
  rw [hspec, hwrap]
  exact ⟨rfl, rfl⟩

/-- Theorem 7 (Edition 2021 -> Edition 2024 Codegen Equivalence):
Wrapping `no_mangle`, `export_name`, or `link_section` in `unsafe(...)` in Edition 2024
produces bit-identical `CodegenAttrs`, `containsExternIndicator`, and `SymbolExportLevel`
as bare attributes in Edition 2021 (both pass `checkAllAttrs`). -/
noncomputable def wrapForEdition2024 (u : AttrUse) : AttrUse :=
  match expectedSafetyOf u.kind with
  | .unsafeSince2024 => { u with annot := .unsafeWrapped, pathSpanEdition := .ed2024 }
  | .normal => { u with pathSpanEdition := .ed2024 }

theorem checkAttr_ed2021_bare_ok (u : AttrUse)
    (hed : u.pathSpanEdition = .ed2021) (han : u.annot = .bare) :
    isAttrError (checkAttributeSafety u) = false := by
  dsimp only [checkAttributeSafety, isAttrError, expectedSafetyOf]
  rw [hed, han]
  cases u.kind <;> rfl

theorem checkAttr_wrap2024_ok (u : AttrUse) (han : u.annot = .bare) :
    isAttrError (checkAttributeSafety (wrapForEdition2024 u)) = false := by
  dsimp only [wrapForEdition2024, expectedSafetyOf, checkAttributeSafety, isAttrError]
  cases u.kind <;> first | rfl | rw [han]

theorem applyOneBuiltinAttr_wrap2024_eq (itemIdent : Nat) (acc : CodegenAttrs) (u : AttrUse) :
    applyOneBuiltinAttr itemIdent acc u =
    applyOneBuiltinAttr itemIdent acc (wrapForEdition2024 u) := by
  dsimp only [applyOneBuiltinAttr, wrapForEdition2024, expectedSafetyOf]
  cases u.kind <;> rfl

theorem checkAllAttrs_ed2021_bare
    (attrs : List AttrUse)
    (h21 : ∀ u, u ∈ attrs → u.pathSpanEdition = .ed2021 ∧ u.annot = .bare) :
    checkAllAttrs attrs = true := by
  induction attrs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hxed, hxan⟩ := h21 x List.mem_cons_self
    have hxs := ih (fun y hy => h21 y (List.mem_cons_of_mem x hy))
    dsimp only [checkAllAttrs]
    rw [checkAttr_ed2021_bare_ok x hxed hxan]
    exact hxs

theorem checkAllAttrs_wrap2024
    (attrs : List AttrUse)
    (h21 : ∀ u, u ∈ attrs → u.pathSpanEdition = .ed2021 ∧ u.annot = .bare) :
    checkAllAttrs (attrs.map wrapForEdition2024) = true := by
  induction attrs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨_, hxan⟩ := h21 x List.mem_cons_self
    have hxs := ih (fun y hy => h21 y (List.mem_cons_of_mem x hy))
    dsimp only [List.map, checkAllAttrs]
    rw [checkAttr_wrap2024_ok x hxan]
    exact hxs

theorem foldl_wrap2024_eq
    (itemIdent : Nat) (attrs : List AttrUse) (init : CodegenAttrs) :
    attrs.foldl (applyOneBuiltinAttr itemIdent) init =
    (attrs.map wrapForEdition2024).foldl (applyOneBuiltinAttr itemIdent) init := by
  induction attrs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [List.map, List.foldl]
    rw [applyOneBuiltinAttr_wrap2024_eq itemIdent init x]
    exact ih _

theorem codegen_equivalence_2021_bare_to_2024_unsafe
    (itemIdent : Nat) (attrs : List AttrUse)
    (h21 : ∀ u, u ∈ attrs → u.pathSpanEdition = .ed2021 ∧ u.annot = .bare) :
    let attrs24 := attrs.map wrapForEdition2024
    checkAllAttrs attrs = true ∧
    checkAllAttrs attrs24 = true ∧
    processBuiltinAttrs itemIdent attrs = processBuiltinAttrs itemIdent attrs24 ∧
    symbolExportLevel (processBuiltinAttrs itemIdent attrs) =
      symbolExportLevel (processBuiltinAttrs itemIdent attrs24) := by
  have hcheck21 := checkAllAttrs_ed2021_bare attrs h21
  have hcheck24 := checkAllAttrs_wrap2024 attrs h21
  have hproc : processBuiltinAttrs itemIdent attrs =
      processBuiltinAttrs itemIdent (attrs.map wrapForEdition2024) :=
    foldl_wrap2024_eq itemIdent attrs CodegenAttrs.empty
  refine ⟨hcheck21, hcheck24, hproc, ?_⟩
  rw [hproc]

/-- Theorem 8 (`#[unsafe(export_name)]` Precedence Over `#[unsafe(no_mangle)]`):
In both attribute orderings (`[noMangle, exportName s]` and `[exportName s, noMangle]`),
`processBuiltinAttrs` sets `symbolName := some s` (`codegen_attrs.rs:73, 109-111`). -/
theorem export_name_precedence_over_no_mangle_both_orders
    (itemIdent sym : Nat) (ed1 ed2 : Edition) (an1 an2 : AttrSafetyAnnot) :
    let uNm : AttrUse := { kind := .noMangle, annot := an1, pathSpanEdition := ed1 }
    let uExp : AttrUse := { kind := .exportName sym, annot := an2, pathSpanEdition := ed2 }
    (processBuiltinAttrs itemIdent [uNm, uExp]).symbolName = some sym ∧
    (processBuiltinAttrs itemIdent [uExp, uNm]).symbolName = some sym := by
  exact ⟨rfl, rfl⟩

/-- Theorem 9 (`#[unsafe(link_section)]` Alone Does Not Mark Extern Export):
Applying `#[unsafe(link_section = s)]` without `no_mangle` or `export_name` keeps
`containsExternIndicator = false` and `symbolExportLevel = .rust`. -/
theorem link_section_alone_does_not_export_c_symbol
    (itemIdent secId : Nat) (ed : Edition) (an : AttrSafetyAnnot) :
    let uLs : AttrUse := { kind := .linkSection secId, annot := an, pathSpanEdition := ed }
    containsExternIndicator (processBuiltinAttrs itemIdent [uLs]) = false ∧
    symbolExportLevel (processBuiltinAttrs itemIdent [uLs]) = .rust := by
  exact ⟨rfl, rfl⟩

/-- Counterexample 5 (Cross-Edition Macro Span Bypass, `safety.rs:53`):
Because `check_attribute_safety` inspects `path_span.edition()` (the edition of the macro
definition emitting `#[no_mangle]`), an Edition 2021 macro injecting bare `#[no_mangle]`
into an Edition 2024 crate bypasses the `errUnsafeAttrOutsideUnsafe` hard error! -/
theorem ce5_cross_edition_macro_bypass (crateEdition : Edition)
    (_h24 : crateEdition = .ed2024) :
    let macroAttr : AttrUse :=
      { kind := .noMangle, annot := .bare, pathSpanEdition := .ed2021 }
    isAttrError (checkAttributeSafety macroAttr) = false ∧
    macroAttr.annot = .bare := by
  exact ⟨rfl, rfl⟩

/-- Combined End-to-End Pipeline Theorem:
For any PIC crate module whose attributes pass `checkAllAttrs`, whose relocations are
in-bounds, and whose statics are routed through `classifyStaticSection .pic`:
1. Every attribute in Edition 2024 requiring `unsafe(...)` has an `unsafeWrapped` witness;
2. Loading preserves all initial bytes;
3. Dynamic relocation (`applyAllRelocs`) succeeds with zero faults;
4. After `applyRelroProtect`, every `WellTypedRuntimeOp` sequence executes with zero `SIGSEGV`
   and preserves all immutable `.rodata` and `.data.rel.ro` contents! -/
theorem end_to_end_static_placement_and_attr_soundness
    (attrs : List AttrUse)
    (decls : List StaticDecl)
    (ops : List RuntimeOp)
    (hattrs_ed24 : ∀ u, u ∈ attrs → u.pathSpanEdition = .ed2024)
    (hattrs_ok : checkAllAttrs attrs = true)
    (hdist : DistinctSymIds (decls.map (emitWithClassifier .pic)))
    (hbounds : ∀ d, d ∈ decls → RelocsInBounds d)
    (hwt : ∀ op, op ∈ ops → WellTypedRuntimeOp (decls.map (emitWithClassifier .pic)) op) :
    (∀ u, u ∈ attrs → expectedSafetyOf u.kind = .unsafeSince2024 → u.annot = .unsafeWrapped) ∧
    (∃ stReloc,
      applyAllRelocs (loadProgram (decls.map (emitWithClassifier .pic)))
                     (decls.map (emitWithClassifier .pic)) = .ok stReloc ∧
      ∃ stEnd,
        execRuntimeTrace (applyRelroProtect stReloc) ops = .ok stEnd ∧
        PostRelroMemSafeInv stEnd (decls.map (emitWithClassifier .pic)) ∧
        (∀ d, d ∈ decls → hasInteriorOrMut d.mutability = false →
          ∀ s0 s1,
            assocLookup (applyRelroProtect stReloc).syms d.symId = some s0 →
            assocLookup stEnd.syms d.symId = some s1 →
            s1.loadedBytes = s0.loadedBytes)) := by
  constructor
  · intro u hu hspec
    have hnoerr : isAttrError (checkAttributeSafety u) = false := by
      clear hdist hbounds hwt hattrs_ed24
      induction attrs with
      | nil => cases hu
      | cons x xs ih =>
        dsimp only [checkAllAttrs] at hattrs_ok
        cases hx : isAttrError (checkAttributeSafety x)
        · rw [hx] at hattrs_ok
          cases hu with
          | head => exact hx
          | tail _ hmem => exact ih hattrs_ok hmem
        · rw [hx] at hattrs_ok; cases hattrs_ok
    exact edition2024_gate_requires_unsafe_witness u hspec (hattrs_ed24 u hu) hnoerr
  · let es := decls.map (emitWithClassifier .pic)
    have hpic : ∀ e, e ∈ es → e = emitWithClassifier .pic e.decl := by
      intro e he
      obtain ⟨d, _, hd⟩ := List.mem_map.mp he
      subst hd
      rfl
    have hbounds_es : ∀ e, e ∈ es → RelocsInBounds e.decl := by
      intro e he
      obtain ⟨d, hd_mem, hd_eq⟩ := List.mem_map.mp he
      subst hd_eq
      exact hbounds d hd_mem
    have hinv0 := picPreRelroInv_loadProgram es hdist hpic
    obtain ⟨stReloc, happReloc, hinvReloc⟩ :=
      pic_applyAllRelocs_succeeds es es (loadProgram es) (fun _ h => h) hinv0 hpic hbounds_es
    have hpostInv := applyRelroProtect_establishes_postRelroMemSafeInv stReloc es hinvReloc hpic
    obtain ⟨stEnd, hexecEnd, hinvEnd, hpres⟩ :=
      wellTypedTrace_safe_and_preserves_immutable (applyRelroProtect stReloc) es ops hpostInv hwt
    refine ⟨stReloc, happReloc, stEnd, hexecEnd, hinvEnd, ?_⟩
    intro d hd_mem hd_imm s0 s1 hs0 hs1
    have he_mem : emitWithClassifier .pic d ∈ es := List.mem_map_of_mem hd_mem
    exact hpres (emitWithClassifier .pic d) he_mem hd_imm s0 s1 hs0 hs1

end StaticElfSectionPlacementAndUnsafeAttrsSoundness
