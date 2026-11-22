/-!
# Reproducible Build Determinism Soundness (`rustc` Path Remapping, Multi-CGU Sorting,
  Deterministic `ar` Archiving, and Incremental Session Nonces)

Self-contained constructive Lean v4.34.1 mechanization using only core `Init`
definitions and total structural recursion.

Models the four primary-source `rustc` determinism mechanisms:
1. `FilePathMapping` reverse-precedence prefix remapping and `RealFileName`
   scope-gated crate-metadata stripping (`rustc_span/src/source_map.rs`,
   `rustc_span/src/lib.rs`, `rustc_metadata/src/rmeta/encoder.rs`).
2. Parallel multi-CGU codegen followed by canonical name-sorted assembly
   (`rustc_codegen_ssa/src/back/write.rs` `OngoingCodegen::join`) and
   canonical zero-epoch `ar` archive serialization
   (`rustc_codegen_ssa/src/back/archive.rs` `NewArchiveMember { mtime: 0, uid: 0, gid: 0, perms: 0o644 }`).
3. The `-C incremental` two-mechanism bit-identity cliff:
   - MIR `Inline` suppression (`rustc_mir_transform/src/inline.rs`) altering
     object code bytes between clean and incremental builds.
   - Per-invocation random 7-char base-36 `invocation_temp` suffixes
     (`rustc_interface/src/util.rs`, `rustc_session/src/config.rs`) written into
     both the GNU `ar` extended filename table (`//`) and `lib.rmeta-link`
     (`rustc_codegen_ssa/src/back/rmeta_link.rs`), preserving object payloads
     and `lib.rmeta` while breaking raw `.rlib` archive hash identity.
4. Diverse Double-Compiling (DDC) and proof-carrying verification receipt
   soundness over raw archive identity vs. payload-normalized equivalence.
-/

namespace ReproducibleBuildDeterminism

/-! ## Section 1: Constructive Equality & Lexicographic Order on Byte Strings (`List Nat`) -/

/-- Constructive boolean equality on `Nat`. -/
noncomputable def natEqBool : Nat → Nat → Bool
  | 0, 0 => true
  | 0, _ + 1 => false
  | _ + 1, 0 => false
  | m + 1, n + 1 => natEqBool m n

theorem natEqBool_refl : ∀ n : Nat, natEqBool n n = true
  | 0 => rfl
  | n + 1 => natEqBool_refl n

/-- Constructive boolean equality on byte sequences (`List Nat`). -/
noncomputable def bytesEqBool : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | x :: xs, y :: ys => if natEqBool x y then bytesEqBool xs ys else false

theorem bytesEqBool_refl : ∀ xs : List Nat, bytesEqBool xs xs = true
  | [] => rfl
  | x :: xs => by
    unfold bytesEqBool
    rw [natEqBool_refl x]
    exact bytesEqBool_refl xs

/-- Constructive strict `<` on `Nat` as a `Bool`. -/
noncomputable def natLtBool : Nat → Nat → Bool
  | 0, 0 => false
  | 0, _ + 1 => true
  | _ + 1, 0 => false
  | m + 1, n + 1 => natLtBool m n

theorem natLtBool_irrefl : ∀ n : Nat, natLtBool n n = false
  | 0 => rfl
  | n + 1 => natLtBool_irrefl n

theorem natLtBool_asym : ∀ m n : Nat, natLtBool m n = true → natLtBool n m = false
  | 0, 0, h => by cases h
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => by cases h
  | m + 1, n + 1, h => natLtBool_asym m n h

theorem natLtBool_trans : ∀ a b c : Nat,
    natLtBool a b = true → natLtBool b c = true → natLtBool a c = true
  | 0, 0, _, hab, _ => by cases hab
  | 0, _ + 1, 0, _, hbc => by cases hbc
  | 0, _ + 1, _ + 1, _, _ => rfl
  | _ + 1, 0, _, hab, _ => by cases hab
  | _ + 1, _ + 1, 0, _, hbc => by cases hbc
  | a + 1, b + 1, c + 1, hab, hbc => natLtBool_trans a b c hab hbc

theorem natLtBool_trichotomy : ∀ m n : Nat,
    natLtBool m n = true ∨ m = n ∨ natLtBool n m = true
  | 0, 0 => Or.inr (Or.inl rfl)
  | 0, _ + 1 => Or.inl rfl
  | _ + 1, 0 => Or.inr (Or.inr rfl)
  | m + 1, n + 1 =>
    match natLtBool_trichotomy m n with
    | Or.inl h => Or.inl h
    | Or.inr (Or.inl h) => Or.inr (Or.inl (congrArg Nat.succ h))
    | Or.inr (Or.inr h) => Or.inr (Or.inr h)

/-- Lexicographic strict order on byte sequences (`List Nat`), modeling `str::cmp`. -/
noncomputable def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    if natLtBool x y then true
    else if natLtBool y x then false
    else lexLt xs ys

theorem lexLt_irrefl : ∀ xs : List Nat, lexLt xs xs = false
  | [] => rfl
  | x :: xs => by
    unfold lexLt
    rw [natLtBool_irrefl x]
    exact lexLt_irrefl xs

theorem lexLt_asym : ∀ xs ys : List Nat, lexLt xs ys = true → lexLt ys xs = false
  | [], [], h => by cases h
  | [], _ :: _, _ => rfl
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    unfold lexLt at h ⊢
    cases hxy : natLtBool x y with
    | true =>
      rw [natLtBool_asym x y hxy]
      cases hyx : natLtBool x y with
      | true => rfl
      | false => rw [hxy] at hyx; cases hyx
    | false =>
      rw [hxy] at h
      cases hyx : natLtBool y x with
      | true =>
        rw [hyx] at h
        cases h
      | false =>
        rw [hyx] at h
        exact lexLt_asym xs ys h

theorem lexLt_trans : ∀ xs ys zs : List Nat,
    lexLt xs ys = true → lexLt ys zs = true → lexLt xs zs = true
  | [], [], _, h1, _ => by cases h1
  | [], _ :: _, [], _, h2 => by cases h2
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h1, _ => by cases h1
  | _ :: _, _ :: _, [], _, h2 => by cases h2
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    unfold lexLt at h1 h2 ⊢
    cases hxy : natLtBool x y with
    | true =>
      cases hyz : natLtBool y z with
      | true =>
        rw [natLtBool_trans x y z hxy hyz]
        rfl
      | false =>
        rw [hyz] at h2
        cases hzy : natLtBool z y with
        | true => rw [hzy] at h2; cases h2
        | false =>
          have hyEqZ : y = z := by
            match natLtBool_trichotomy y z with
            | Or.inl h => rw [h] at hyz; cases hyz
            | Or.inr (Or.inl h) => exact h
            | Or.inr (Or.inr h) => rw [h] at hzy; cases hzy
          subst hyEqZ
          rw [hxy]
          rfl
    | false =>
      rw [hxy] at h1
      cases hyx : natLtBool y x with
      | true => rw [hyx] at h1; cases h1
      | false =>
        rw [hyx] at h1
        have hxEqY : x = y := by
          match natLtBool_trichotomy x y with
          | Or.inl h => rw [h] at hxy; cases hxy
          | Or.inr (Or.inl h) => exact h
          | Or.inr (Or.inr h) => rw [h] at hyx; cases hyx
        subst hxEqY
        cases hyz : natLtBool x z with
        | true => rfl
        | false =>
          rw [hyz] at h2
          cases hzx : natLtBool z x with
          | true => rw [hzx] at h2; cases h2
          | false =>
            rw [hzx] at h2
            exact lexLt_trans xs ys zs h1 h2

theorem lexLt_trichotomy : ∀ xs ys : List Nat,
    lexLt xs ys = true ∨ xs = ys ∨ lexLt ys xs = true
  | [], [] => Or.inr (Or.inl rfl)
  | [], _ :: _ => Or.inl rfl
  | _ :: _, [] => Or.inr (Or.inr rfl)
  | x :: xs, y :: ys =>
    match natLtBool_trichotomy x y with
    | Or.inl hxy =>
      Or.inl (by unfold lexLt; rw [hxy]; rfl)
    | Or.inr (Or.inr hyx) =>
      Or.inr (Or.inr (by unfold lexLt; rw [hyx]; rfl))
    | Or.inr (Or.inl hEq) => by
      subst hEq
      match lexLt_trichotomy xs ys with
      | Or.inl hlt =>
        exact Or.inl (by unfold lexLt; rw [natLtBool_irrefl x]; exact hlt)
      | Or.inr (Or.inl htail) =>
        exact Or.inr (Or.inl (congrArg (List.cons x) htail))
      | Or.inr (Or.inr hgt) =>
        exact Or.inr (Or.inr (by unfold lexLt; rw [natLtBool_irrefl x]; exact hgt))

/-! ## Section 2: Path Remapping (`FilePathMapping` & `RealFileName`) -/

/-- A path represented as a sequence of directory/file component byte strings (`List Nat`). -/
abbrev PathSegs := List (List Nat)

/-- Exact scope modes modeled after `RemapPathScopeComponents`. -/
inductive RemapScope where
  | none
  | objectOnly -- `macro | debuginfo | coverage` (excludes `diagnostics`)
  | all        -- default `--remap-path-scope=all`
  deriving DecidableEq, Repr

/-- A single `--remap-path-prefix=from=to` rule. -/
structure RemapRule where
  fromPrefix : PathSegs
  toPrefix : PathSegs
  deriving DecidableEq, Repr

/-- `FilePathMapping` storing rules in CLI order plus active scope. -/
structure FilePathMapping where
  rules : List RemapRule
  scope : RemapScope
  deriving DecidableEq, Repr

/-- Strip prefix `pfx` from `path` if `pfx` is a component-wise prefix. -/
noncomputable def stripPrefix : PathSegs → PathSegs → Option PathSegs
  | [], rest => some rest
  | p :: ps, x :: xs => if bytesEqBool p x then stripPrefix ps xs else none
  | _ :: _, [] => none

theorem stripPrefix_append : ∀ pfx rel : PathSegs,
    stripPrefix pfx (pfx ++ rel) = some rel
  | [], _ => rfl
  | p :: ps, rel => by
    simp only [List.cons_append, stripPrefix, bytesEqBool_refl, ↓reduceIte]
    exact stripPrefix_append ps rel

/-- Try rules in order (caller passes `rules.reverse` to match `mapping.iter().rev()`). -/
noncomputable def applyRulesRev : List RemapRule → PathSegs → PathSegs × Bool
  | [], path => (path, false)
  | r :: rs, path =>
    match stripPrefix r.fromPrefix path with
    | some rest => (r.toPrefix ++ rest, true)
    | none => applyRulesRev rs path

/-- Matches `FilePathMapping::map_prefix` (`source_map.rs:1141-1179`), applying later
    CLI rules first (`rules.reverse`). -/
noncomputable def mapPrefix (m : FilePathMapping) (path : PathSegs) : PathSegs × Bool :=
  applyRulesRev m.rules.reverse path

/-- Models `InnerRealFileName` (`rustc_span/src/lib.rs:317-324`). -/
structure InnerRealFileName where
  name : PathSegs
  workingDirectory : PathSegs
  embeddableName : PathSegs
  deriving DecidableEq, Repr

/-- Models `RealFileName` (`rustc_span/src/lib.rs:304-311`). -/
structure RealFileName where
  localPart : Option InnerRealFileName
  maybeRemapped : InnerRealFileName
  scopes : RemapScope
  deriving DecidableEq, Repr

/-- Models `FilePathMapping::to_real_filename` for an absolute source path under `cwd`. -/
noncomputable def toRealFileName (m : FilePathMapping) (cwd : PathSegs) (relFile : PathSegs) : RealFileName :=
  let absPath := cwd ++ relFile
  let (remappedCwd, cwdRemapped) := mapPrefix m cwd
  let (remappedAbs, pathRemapped) := mapPrefix m absPath
  let anyRemapped := pathRemapped || cwdRemapped
  { localPart := some { name := absPath, workingDirectory := cwd, embeddableName := absPath }
    maybeRemapped := {
      name := remappedAbs
      workingDirectory := remappedCwd
      embeddableName := remappedAbs
    }
    scopes := if anyRemapped then m.scope else RemapScope.none }

/-- Models `RealFileName::update_for_crate_metadata` (`rustc_span/src/lib.rs:476-484`).
    Clears `localPart` ONLY when fully remapped (`.all`) or not remapped at all (`.none`). -/
noncomputable def updateForCrateMetadata (rf : RealFileName) : RealFileName :=
  match rf.scopes with
  | RemapScope.all => { rf with localPart := none }
  | RemapScope.none => { rf with localPart := none }
  | RemapScope.objectOnly => rf

/-- Path emitted into `#[track_caller]` / `file!()` (`RemapPathScopeComponents::MACRO`). -/
noncomputable def macroScopePath (rf : RealFileName) : PathSegs :=
  match rf.scopes with
  | RemapScope.none =>
    match rf.localPart with
    | some loc => loc.name
    | none => rf.maybeRemapped.name
  | RemapScope.objectOnly => rf.maybeRemapped.name
  | RemapScope.all => rf.maybeRemapped.name

/-- `(DW_AT_comp_dir, DW_AT_name)` emitted into DWARF (`RemapPathScopeComponents::DEBUGINFO`). -/
noncomputable def debuginfoPaths (rf : RealFileName) : PathSegs × PathSegs :=
  match rf.scopes with
  | RemapScope.none =>
    match rf.localPart with
    | some loc => (loc.workingDirectory, loc.embeddableName)
    | none => (rf.maybeRemapped.workingDirectory, rf.maybeRemapped.embeddableName)
  | RemapScope.objectOnly => (rf.maybeRemapped.workingDirectory, rf.maybeRemapped.embeddableName)
  | RemapScope.all => (rf.maybeRemapped.workingDirectory, rf.maybeRemapped.embeddableName)

/-- Predicate asserting that `mapping` completely remaps `cwd` to canonical virtual root `vroot`
    under full scope `.all` (i.e., the highest-precedence rule maps `cwd ↦ vroot`). -/
structure CompleteCwdRemap (m : FilePathMapping) (cwd vroot : PathSegs) : Prop where
  scopeAll : m.scope = RemapScope.all
  mapsCwd : ∀ rel : PathSegs, mapPrefix m (cwd ++ rel) = (vroot ++ rel, true)

/-- Standard single-rule `--remap-path-prefix=<cwd>=<vroot>` with default `--remap-path-scope=all`
    satisfies `CompleteCwdRemap`. -/
theorem singleRule_completeCwdRemap (cwd vroot : PathSegs) :
    CompleteCwdRemap { rules := [{ fromPrefix := cwd, toPrefix := vroot }], scope := RemapScope.all } cwd vroot where
  scopeAll := rfl
  mapsCwd := fun rel => by
    unfold mapPrefix applyRulesRev
    change (match stripPrefix cwd (cwd ++ rel) with
      | some rest => (vroot ++ rest, true)
      | none => (cwd ++ rel, false)) = (vroot ++ rel, true)
    rw [stripPrefix_append]

/-- Appending `-Z remap-cwd-prefix=<vroot>` as the final rule (highest precedence under
    `rules.reverse`) satisfies `CompleteCwdRemap` regardless of earlier prefix rules. -/
theorem trailingCwdRule_completeCwdRemap (earlier : List RemapRule) (cwd vroot : PathSegs) :
    CompleteCwdRemap
      { rules := earlier ++ [{ fromPrefix := cwd, toPrefix := vroot }], scope := RemapScope.all }
      cwd vroot where
  scopeAll := rfl
  mapsCwd := fun rel => by
    unfold mapPrefix
    rw [List.reverse_append]
    change (match stripPrefix cwd (cwd ++ rel) with
      | some rest => (vroot ++ rest, true)
      | none => applyRulesRev earlier.reverse (cwd ++ rel)) = (vroot ++ rel, true)
    rw [stripPrefix_append]

theorem completeCwdRemap_cwd_itself {m : FilePathMapping} {cwd vroot : PathSegs}
    (hc : CompleteCwdRemap m cwd vroot) :
    mapPrefix m cwd = (vroot, true) := by
  have h := hc.mapsCwd []
  rw [List.append_nil, List.append_nil] at h
  exact h

/-- Theorem 1a: Complete remapping eliminates `cwd` dependence from crate metadata,
    `#[track_caller]` macro paths, and DWARF debuginfo paths. -/
theorem remap_eliminates_cwd_dependence
    {m1 m2 : FilePathMapping} {cwd1 cwd2 vroot relFile : PathSegs}
    (h1 : CompleteCwdRemap m1 cwd1 vroot)
    (h2 : CompleteCwdRemap m2 cwd2 vroot) :
    let rf1 := toRealFileName m1 cwd1 relFile
    let rf2 := toRealFileName m2 cwd2 relFile
    updateForCrateMetadata rf1 = updateForCrateMetadata rf2 ∧
    macroScopePath rf1 = macroScopePath rf2 ∧
    debuginfoPaths rf1 = debuginfoPaths rf2 := by
  dsimp only [toRealFileName]
  rw [completeCwdRemap_cwd_itself h1, completeCwdRemap_cwd_itself h2]
  rw [h1.mapsCwd relFile, h2.mapsCwd relFile]
  rw [h1.scopeAll, h2.scopeAll]
  exact ⟨rfl, rfl, rfl⟩

/-! ## Section 3: Compiler Pipeline, Multi-CGU Sorting, Canonical `ar`, and Incremental Mode -/

/-- Optimization level (`-C opt-level`). -/
inductive OptLevel where
  | o0
  | o1
  | o2
  | o3
  deriving DecidableEq, Repr

/-- Debuginfo level (`-C debuginfo=0|2`). -/
inductive DebugInfoLevel where
  | d0
  | d2
  deriving DecidableEq, Repr

/-- Incremental session configuration (`-C incremental`).
    When `some nonce`, models `OutputFilenames.invocation_temp` (7-char base-36 token). -/
inductive IncrementalSession where
  | clean
  | incremental (nonce : List Nat)
  deriving DecidableEq, Repr

/-- Abstract source module in a crate. -/
structure SourceModule where
  relFile : PathSegs
  modId : Nat
  usesTrackCaller : Bool
  hasInlineableHelper : Bool
  deriving DecidableEq, Repr

/-- Source crate input independent of host checkout directory `cwd`. -/
structure SourceTree where
  crateName : List Nat
  modules : List SourceModule
  deriving DecidableEq, Repr

/-- CGU plan item before codegen. -/
structure CguPlanItem where
  baseName : List Nat -- canonical CGU identifier bytes (e.g. `cgu.0` or 25-char hash)
  mod : SourceModule
  deriving DecidableEq, Repr

/-- Models `compiler/rustc_mir_transform/src/inline.rs:45-59` (`14210df0e` / `342d74463`):
    at default MIR opt level 2 under `-O2`/`-O3`, MIR `Inline` is enabled iff
    `incremental == None` (unless overridden by `forceInline`). -/
noncomputable def mirInlineEnabled (opt : OptLevel) (incr : IncrementalSession) (forceInline : Option Bool := none) : Bool :=
  match forceInline with
  | some b => b
  | none =>
    match opt, incr with
    | OptLevel.o2, IncrementalSession.clean => true
    | OptLevel.o3, IncrementalSession.clean => true
    | _, _ => false

/-- Abstract serialized crate metadata (`lib.rmeta`). -/
structure RmetaArtifact where
  crateName : List Nat
  sourceFiles : List RealFileName
  mirInlined : Bool
  incrementalMode : Bool
  deriving DecidableEq, Repr

/-- Abstract compiled object file payload (`.rcgu.o`), explicitly separating code bytes,
    `.rodata` (`#[track_caller]`), and DWARF/bitcode path metadata. -/
structure ObjectPayload where
  codeTag : Nat         -- 1 = MIR-inlined codegen, 0 = un-inlined MIR codegen
  rodataPaths : List PathSegs
  dwarfPaths : List (PathSegs × PathSegs)
  deriving DecidableEq, Repr

/-- A compiled CGU produced by a backend worker thread. -/
structure CompiledCgu where
  cguName : List Nat       -- sort key (`CompiledModule.name`)
  memberFileName : List Nat -- basename placed in `ar //` and `lib.rmeta-link`
  payload : ObjectPayload
  deriving DecidableEq, Repr

/-- Canonical `ar` archive header fields matching `ArArchiveBuilder::build_inner`
    (`compiler/rustc_codegen_ssa/src/back/archive.rs:576-584` / `677-685`). -/
structure ArHeader where
  memberName : List Nat
  mtime : Nat
  uid : Nat
  gid : Nat
  perms : Nat
  deriving DecidableEq, Repr

noncomputable def canonicalArHeader (name : List Nat) : ArHeader :=
  { memberName := name, mtime := 0, uid := 0, gid := 0, perms := 0o644 }

/-- Models `lib.rmeta-link` (`compiler/rustc_codegen_ssa/src/back/rmeta_link.rs:17-19`). -/
structure RmetaLinkArtifact where
  rustObjectFiles : List (List Nat)
  deriving DecidableEq, Repr

/-- Complete GNU `ar` `.rlib` archive representation, explicitly tracking:
    - GNU `//` extended filename table (`gnuStrtab`),
    - `lib.rmeta` member,
    - `lib.rmeta-link` member (recording `.rcgu.o` member basenames!),
    - ordered `.rcgu.o` members with canonical zeroed `ArHeader`s. -/
structure ArArchive where
  gnuStrtab : List (List Nat)
  rmetaHeader : ArHeader
  rmetaBody : RmetaArtifact
  rmetaLinkHeader : ArHeader
  rmetaLinkBody : RmetaLinkArtifact
  objEntries : List (ArHeader × ObjectPayload)
  deriving DecidableEq, Repr

/-- Final linked ELF executable image: depends ONLY on the ordered object payloads
    (the linker reads object sections, not `ar` member basenames or `lib.rmeta-link`). -/
structure ElfArtifact where
  linkedPayloads : List ObjectPayload
  deriving DecidableEq, Repr

/-- Full build output tuple `(rmeta, objs, arArchive, elf)`. -/
structure BuildOutput where
  rmeta : RmetaArtifact
  objs : List CompiledCgu
  arArchive : ArArchive
  elf : ElfArtifact
  deriving DecidableEq, Repr

/-! ## Section 4: Canonical CGU Sorting & Parallel Thread-Schedule Permutation Invariance -/

/-- Insertion sort on `CompiledCgu` by lexicographic `cguName`, modeling
    `compiled_modules.modules.sort_by(|a, b| a.name.cmp(&b.name))`
    (`compiler/rustc_codegen_ssa/src/back/write.rs:2181` / `2207`). -/
noncomputable def insertCgu (x : CompiledCgu) : List CompiledCgu → List CompiledCgu
  | [] => [x]
  | y :: ys =>
    if lexLt x.cguName y.cguName then
      x :: y :: ys
    else
      y :: insertCgu x ys

noncomputable def sortCgus : List CompiledCgu → List CompiledCgu
  | [] => []
  | x :: xs => insertCgu x (sortCgus xs)

/-- Inductive list permutation relation (modeling arbitrary parallel worker completion order). -/
inductive Perm {α : Type} : List α → List α → Prop where
  | nil : Perm [] []
  | cons (x : α) {xs ys : List α} : Perm xs ys → Perm (x :: xs) (x :: ys)
  | swap (x y : α) (xs : List α) : Perm (y :: x :: xs) (x :: y :: xs)
  | trans {xs ys zs : List α} : Perm xs ys → Perm ys zs → Perm xs zs

/-- Membership predicate on lists. -/
inductive MemList {α : Type} (a : α) : List α → Prop where
  | head (xs : List α) : MemList a (a :: xs)
  | tail {x : α} {xs : List α} : MemList a xs → MemList a (x :: xs)

theorem perm_mem {α : Type} {xs ys : List α} (hp : Perm xs ys) :
    ∀ {a : α}, MemList a xs → MemList a ys := by
  induction hp with
  | nil => intro a h; exact h
  | cons x _ ih =>
    intro a h
    cases h with
    | head _ => exact MemList.head _
    | tail ht => exact MemList.tail (ih ht)
  | swap x y zs =>
    intro a h
    cases h with
    | head _ => exact MemList.tail (MemList.head _)
    | tail ht =>
      cases ht with
      | head _ => exact MemList.head _
      | tail ht2 => exact MemList.tail (MemList.tail ht2)
  | trans _ _ ih1 ih2 =>
    intro a h
    exact ih2 (ih1 h)

theorem perm_symm {α : Type} {xs ys : List α} (hp : Perm xs ys) : Perm ys xs := by
  induction hp with
  | nil => exact Perm.nil
  | cons x _ ih => exact Perm.cons x ih
  | swap x y zs => exact Perm.swap y x zs
  | trans _ _ ih1 ih2 => exact Perm.trans ih2 ih1

/-- Every `CompiledCgu` in a list has a distinct `cguName` (enforced by `rustc` CGU naming). -/
inductive DistinctCguNames : List CompiledCgu → Prop where
  | nil : DistinctCguNames []
  | cons {x : CompiledCgu} {xs : List CompiledCgu} :
      (∀ y, MemList y xs → x.cguName ≠ y.cguName) →
      DistinctCguNames xs →
      DistinctCguNames (x :: xs)

theorem perm_distinctCguNames {xs ys : List CompiledCgu}
    (hp : Perm xs ys) (hd : DistinctCguNames xs) : DistinctCguNames ys := by
  induction hp with
  | nil => exact DistinctCguNames.nil
  | cons x hp' ih =>
    cases hd with
    | cons hfresh hdxs =>
      apply DistinctCguNames.cons
      · intro y hy
        exact hfresh y (perm_mem (perm_symm hp') hy)
      · exact ih hdxs
  | swap x y zs =>
    cases hd with
    | cons hfreshY hdX =>
      cases hdX with
      | cons hfreshX hdzs =>
        apply DistinctCguNames.cons
        · intro w hw
          cases hw with
          | head _ =>
            intro heq
            exact hfreshY x (MemList.head zs) heq.symm
          | tail hmem =>
            exact hfreshX w hmem
        · apply DistinctCguNames.cons
          · intro w hw
            exact hfreshY w (MemList.tail hw)
          · exact hdzs
  | trans _ _ ih1 ih2 =>
    exact ih2 (ih1 hd)

/-- Key commutation lemma: inserting two CGUs with distinct names commutes regardless
    of which worker thread finished first. -/
theorem insertCgu_comm (x y : CompiledCgu) (hne : x.cguName ≠ y.cguName) :
    ∀ xs : List CompiledCgu, insertCgu x (insertCgu y xs) = insertCgu y (insertCgu x xs)
  | [] => by
    simp only [insertCgu]
    match lexLt_trichotomy x.cguName y.cguName with
    | Or.inl hxy =>
      rw [hxy, lexLt_asym _ _ hxy]; rfl
    | Or.inr (Or.inl heq) =>
      exact False.elim (hne heq)
    | Or.inr (Or.inr hyx) =>
      rw [hyx, lexLt_asym _ _ hyx]; rfl
  | z :: zs => by
    simp only [insertCgu]
    cases hxz : lexLt x.cguName z.cguName with
    | true =>
      cases hyz : lexLt y.cguName z.cguName with
      | true =>
        simp only [insertCgu, hxz, hyz, ↓reduceIte]
        match lexLt_trichotomy x.cguName y.cguName with
        | Or.inl hxy =>
          rw [hxy, lexLt_asym _ _ hxy]; rfl
        | Or.inr (Or.inl heq) =>
          exact False.elim (hne heq)
        | Or.inr (Or.inr hyx) =>
          rw [hyx, lexLt_asym _ _ hyx]; rfl
      | false =>
        simp only [insertCgu, hxz, hyz, Bool.false_eq_true, ↓reduceIte]
        have hxy : lexLt x.cguName y.cguName = true := by
          match lexLt_trichotomy z.cguName y.cguName with
          | Or.inl hzy => exact lexLt_trans _ _ _ hxz hzy
          | Or.inr (Or.inl hzyEq) => rw [← hzyEq]; exact hxz
          | Or.inr (Or.inr hyz') => rw [hyz'] at hyz; cases hyz
        rw [lexLt_asym _ _ hxy]; rfl
    | false =>
      cases hyz : lexLt y.cguName z.cguName with
      | true =>
        simp only [insertCgu, hxz, hyz, Bool.false_eq_true, ↓reduceIte]
        have hyx : lexLt y.cguName x.cguName = true := by
          match lexLt_trichotomy z.cguName x.cguName with
          | Or.inl hzx => exact lexLt_trans _ _ _ hyz hzx
          | Or.inr (Or.inl hzxEq) => rw [← hzxEq]; exact hyz
          | Or.inr (Or.inr hxz') => rw [hxz'] at hxz; cases hxz
        rw [lexLt_asym _ _ hyx]; rfl
      | false =>
        simp only [insertCgu, hxz, hyz, Bool.false_eq_true, ↓reduceIte]
        exact congrArg (List.cons z) (insertCgu_comm x y hne zs)

/-- Canonical sorting is invariant under arbitrary thread-completion permutations
    whenever CGU names are distinct. -/
theorem sortCgus_eq_of_perm {xs ys : List CompiledCgu}
    (hp : Perm xs ys) (hd : DistinctCguNames xs) :
    sortCgus xs = sortCgus ys := by
  induction hp with
  | nil => rfl
  | cons x hp' ih =>
    cases hd with
    | cons _ hdxs =>
      unfold sortCgus
      exact congrArg (insertCgu x) (ih hdxs)
  | swap x y zs =>
    cases hd with
    | cons hfreshY _ =>
      unfold sortCgus
      have hne : y.cguName ≠ x.cguName := hfreshY x (MemList.head zs)
      exact insertCgu_comm y x hne (sortCgus zs)
  | trans hp1 hp2 ih1 ih2 =>
    have hdMid := perm_distinctCguNames hp1 hd
    exact Eq.trans (ih1 hd) (ih2 hdMid)

/-! ## Section 5: Full Pipeline Definition (`compilePipeline`) -/

/-- Compute the `.rcgu.o` archive member name:
    - clean: `<baseName>.rcgu.o` (modeled as `baseName ++ [46, 111]`)
    - incremental: `<baseName>.<nonce>.rcgu.o` (modeled as `baseName ++ [46] ++ nonce ++ [46, 111]`). -/
noncomputable def makeMemberName (baseName : List Nat) (incr : IncrementalSession) : List Nat :=
  match incr with
  | IncrementalSession.clean => baseName ++ [46, 111]
  | IncrementalSession.incremental nonce => baseName ++ [46] ++ nonce ++ [46, 111]

/-- Compile a single CGU plan item deterministically given remapping, opt/debug, and incremental mode. -/
noncomputable def compileOneCgu
    (cwd : PathSegs)
    (mapping : FilePathMapping)
    (opt : OptLevel)
    (dbg : DebugInfoLevel)
    (incr : IncrementalSession)
    (item : CguPlanItem) : CompiledCgu :=
  let rf := toRealFileName mapping cwd item.mod.relFile
  let codeTag :=
    if item.mod.hasInlineableHelper && mirInlineEnabled opt incr then 1 else 0
  let rodataPaths :=
    if item.mod.usesTrackCaller then [macroScopePath rf] else []
  let dwarfPaths :=
    match dbg with
    | DebugInfoLevel.d0 => []
    | DebugInfoLevel.d2 => [debuginfoPaths rf]
  { cguName := item.baseName
    memberFileName := makeMemberName item.baseName incr
    payload := { codeTag := codeTag, rodataPaths := rodataPaths, dwarfPaths := dwarfPaths } }

/-- Assemble canonical GNU `ar` `.rlib` and linked ELF from an arbitrary-order list of
    worker-completed `CompiledCgu`s by sorting first (`OngoingCodegen::join`). -/
noncomputable def assembleArtifacts (rmeta : RmetaArtifact) (workerOutputs : List CompiledCgu) : BuildOutput :=
  let sorted := sortCgus workerOutputs
  let objNames := sorted.map (fun c => c.memberFileName)
  let rmetaLink : RmetaLinkArtifact := { rustObjectFiles := objNames }
  let archive : ArArchive :=
    { gnuStrtab := objNames
      rmetaHeader := canonicalArHeader [108, 105, 98, 46, 114, 109, 101, 116, 97]
      rmetaBody := rmeta
      rmetaLinkHeader := canonicalArHeader [108, 105, 98, 46, 114, 109, 101, 116, 97, 45, 108]
      rmetaLinkBody := rmetaLink
      objEntries := sorted.map (fun c => (canonicalArHeader c.memberFileName, c.payload)) }
  let elf : ElfArtifact :=
    { linkedPayloads := sorted.map (fun c => c.payload) }
  { rmeta := rmeta, objs := sorted, arArchive := archive, elf := elf }

/-- End-to-end `rustc` build pipeline parameterized by `(sourceTree, cwd, remapRules, cguPlan,
    optLevel, debugInfo, incrementalSession)`. -/
noncomputable def compilePipeline
    (src : SourceTree)
    (cwd : PathSegs)
    (mapping : FilePathMapping)
    (cguPlan : List CguPlanItem)
    (opt : OptLevel)
    (dbg : DebugInfoLevel)
    (incr : IncrementalSession) : BuildOutput :=
  let sourceFiles := src.modules.map (fun m => updateForCrateMetadata (toRealFileName mapping cwd m.relFile))
  let isIncr := match incr with | IncrementalSession.clean => false | IncrementalSession.incremental _ => true
  let rmeta : RmetaArtifact :=
    { crateName := src.crateName
      sourceFiles := sourceFiles
      mirInlined := mirInlineEnabled opt incr
      incrementalMode := isIncr }
  let compiled := cguPlan.map (compileOneCgu cwd mapping opt dbg incr)
  assembleArtifacts rmeta compiled

/-! ## Section 6: Core Determinism Theorems -/

/-- Helper: mapping `updateForCrateMetadata ∘ toRealFileName` over `modules` is invariant under
    `CompleteCwdRemap`. -/
theorem map_updateForCrateMetadata_eq
    {m1 m2 : FilePathMapping} {cwd1 cwd2 vroot : PathSegs}
    (h1 : CompleteCwdRemap m1 cwd1 vroot)
    (h2 : CompleteCwdRemap m2 cwd2 vroot) :
    ∀ mods : List SourceModule,
      mods.map (fun m => updateForCrateMetadata (toRealFileName m1 cwd1 m.relFile)) =
      mods.map (fun m => updateForCrateMetadata (toRealFileName m2 cwd2 m.relFile))
  | [] => rfl
  | m :: ms => by
    simp only [List.map]
    have hhead := (remap_eliminates_cwd_dependence h1 h2 (relFile := m.relFile)).1
    rw [hhead, map_updateForCrateMetadata_eq h1 h2 ms]

/-- Helper: compiling every CGU in `cguPlan` is invariant under `CompleteCwdRemap`. -/
theorem map_compileOneCgu_eq
    {m1 m2 : FilePathMapping} {cwd1 cwd2 vroot : PathSegs}
    (h1 : CompleteCwdRemap m1 cwd1 vroot)
    (h2 : CompleteCwdRemap m2 cwd2 vroot)
    (opt : OptLevel) (dbg : DebugInfoLevel) (incr : IncrementalSession) :
    ∀ plan : List CguPlanItem,
      plan.map (compileOneCgu cwd1 m1 opt dbg incr) =
      plan.map (compileOneCgu cwd2 m2 opt dbg incr)
  | [] => rfl
  | item :: rest => by
    simp only [List.map]
    have hdep := remap_eliminates_cwd_dependence h1 h2 (relFile := item.mod.relFile)
    have hhead : compileOneCgu cwd1 m1 opt dbg incr item = compileOneCgu cwd2 m2 opt dbg incr item := by
      dsimp only [compileOneCgu]
      rw [hdep.2.1, hdep.2.2]
    rw [hhead, map_compileOneCgu_eq h1 h2 opt dbg incr rest]

/-- **Theorem 1: Cross-Directory Bit-Exactness Under Complete Path Remapping.**
    Given any two distinct checkout directories `cwd1` and `cwd2` mapped to the same virtual
    prefix `vroot` with scope `.all`, the entire build output `(rmeta, objs, arArchive, elf)`
    is bit-for-bit identical across `cwd1` and `cwd2` at every optimization and debuginfo level. -/
theorem remap_complete_implies_cross_dir_bit_exact
    (src : SourceTree) (cguPlan : List CguPlanItem)
    (cwd1 cwd2 vroot : PathSegs)
    (m1 m2 : FilePathMapping)
    (opt : OptLevel) (dbg : DebugInfoLevel) (incr : IncrementalSession)
    (h1 : CompleteCwdRemap m1 cwd1 vroot)
    (h2 : CompleteCwdRemap m2 cwd2 vroot) :
    compilePipeline src cwd1 m1 cguPlan opt dbg incr =
    compilePipeline src cwd2 m2 cguPlan opt dbg incr := by
  unfold compilePipeline
  rw [map_updateForCrateMetadata_eq h1 h2 src.modules]
  rw [map_compileOneCgu_eq h1 h2 opt dbg incr cguPlan]

/-- **Theorem 2: Parallel CGU Permutation Invariance Under Sorted Canonical Archive Assembly.**
    If two parallel `-C codegen-units=N -Z threads=T` runs finish compiling the same CGUs
    in arbitrary permuted thread completion orders `sched1` and `sched2` (`Perm sched1 sched2`),
    canonical sorting (`sortCgus`) plus zero-epoch `ar` header assembly guarantees bit-exact
    equality of `(rmeta, objs, arArchive, elf)`. -/
theorem sorted_cgu_archive_invariant_under_thread_schedule
    (rmeta : RmetaArtifact)
    (sched1 sched2 : List CompiledCgu)
    (hperm : Perm sched1 sched2)
    (hdist : DistinctCguNames sched1) :
    assembleArtifacts rmeta sched1 = assembleArtifacts rmeta sched2 := by
  unfold assembleArtifacts
  rw [sortCgus_eq_of_perm hperm hdist]

/-- Payload-normalized projection of an `ArArchive`: erases session-varying `ar` member
    basenames (`gnuStrtab`, `rmetaLink`, `ArHeader.memberName`) while retaining `rmeta`
    and every `.rcgu.o` object payload in canonical CGU order. -/
noncomputable def normalizedArchivePayload (a : ArArchive) : RmetaArtifact × List ObjectPayload :=
  (a.rmetaBody, a.objEntries.map Prod.snd)

theorem insertCgu_cguName_eq (f : CompiledCgu → CompiledCgu)
    (hname : ∀ c, (f c).cguName = c.cguName) :
    ∀ x xs, insertCgu (f x) (xs.map f) = (insertCgu x xs).map f
  | _, [] => rfl
  | x, y :: ys => by
    simp only [List.map, insertCgu, hname]
    cases hlt : lexLt x.cguName y.cguName with
    | true => rfl
    | false =>
      exact congrArg (List.cons (f y)) (insertCgu_cguName_eq f hname x ys)

theorem sortCgus_map_key_preserving (f : CompiledCgu → CompiledCgu)
    (hname : ∀ c, (f c).cguName = c.cguName) :
    ∀ xs, sortCgus (xs.map f) = (sortCgus xs).map f
  | [] => rfl
  | x :: xs => by
    simp only [List.map, sortCgus]
    rw [sortCgus_map_key_preserving f hname xs]
    exact insertCgu_cguName_eq f hname x (sortCgus xs)

theorem makeMemberName_injective_nonce (base n1 n2 : List Nat)
    (h : makeMemberName base (IncrementalSession.incremental n1) =
         makeMemberName base (IncrementalSession.incremental n2)) :
    n1 = n2 := by
  unfold makeMemberName at h
  have h1 : [46] ++ n1 ++ [46, 111] = [46] ++ n2 ++ [46, 111] := by
    have h' : base ++ ([46] ++ n1 ++ [46, 111]) = base ++ ([46] ++ n2 ++ [46, 111]) := by
      simpa [List.append_assoc] using h
    exact List.append_cancel_left h'
  have h2 : n1 ++ [46, 111] = n2 ++ [46, 111] := by
    injection h1
  exact List.append_cancel_right h2

/-- **Theorem 3: Payload-Equivalence vs. Archive-Hash Sensitivity Under Incremental Session Nonces.**
    Changing only the incremental `invocation_temp` nonce (`n1 ≠ n2`) on a non-empty CGU plan:
    (a) preserves `rmeta` bit-for-bit,
    (b) preserves every `.rcgu.o` `ObjectPayload` (and `normalizedArchivePayload`) bit-for-bit,
    (c) preserves the linked `elf` bit-for-bit, YET
    (d) breaks raw `arArchive` equality (both `gnuStrtab` and `rmetaLinkBody` differ!). -/
theorem incremental_nonce_preserves_payload_breaks_archive_hash
    (src : SourceTree) (cwd : PathSegs) (mapping : FilePathMapping)
    (firstItem : CguPlanItem) (restItems : List CguPlanItem)
    (opt : OptLevel) (dbg : DebugInfoLevel)
    (n1 n2 : List Nat) (hne : n1 ≠ n2) :
    let plan := firstItem :: restItems
    let b1 := compilePipeline src cwd mapping plan opt dbg (IncrementalSession.incremental n1)
    let b2 := compilePipeline src cwd mapping plan opt dbg (IncrementalSession.incremental n2)
    b1.rmeta = b2.rmeta ∧
    normalizedArchivePayload b1.arArchive = normalizedArchivePayload b2.arArchive ∧
    b1.elf = b2.elf ∧
    b1.arArchive ≠ b2.arArchive := by
  dsimp only
  let plan := firstItem :: restItems
  let retag : CompiledCgu → CompiledCgu :=
    fun c => { c with memberFileName := makeMemberName c.cguName (IncrementalSession.incremental n2) }
  have hRetagMap : ∀ ps : List CguPlanItem,
      ps.map (compileOneCgu cwd mapping opt dbg (IncrementalSession.incremental n2)) =
      (ps.map (compileOneCgu cwd mapping opt dbg (IncrementalSession.incremental n1))).map retag := by
    intro ps
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.map, ih]
      have hHead :
          compileOneCgu cwd mapping opt dbg (IncrementalSession.incremental n2) p =
          retag (compileOneCgu cwd mapping opt dbg (IncrementalSession.incremental n1) p) := by
        dsimp only [compileOneCgu, retag, mirInlineEnabled]
        cases opt <;> rfl
      rw [hHead]
  have hSortRel :
      sortCgus (plan.map (compileOneCgu cwd mapping opt dbg (IncrementalSession.incremental n2))) =
      (sortCgus (plan.map (compileOneCgu cwd mapping opt dbg (IncrementalSession.incremental n1)))).map retag := by
    rw [hRetagMap plan]
    exact sortCgus_map_key_preserving retag (fun _ => rfl) _
  have hRmetaEq :
      (compilePipeline src cwd mapping plan opt dbg (IncrementalSession.incremental n1)).rmeta =
      (compilePipeline src cwd mapping plan opt dbg (IncrementalSession.incremental n2)).rmeta := by
    unfold compilePipeline assembleArtifacts mirInlineEnabled
    cases opt <;> rfl
  have hPayloadsEq :
      (sortCgus (plan.map (compileOneCgu cwd mapping opt dbg (IncrementalSession.incremental n2)))).map (fun c => c.payload) =
      (sortCgus (plan.map (compileOneCgu cwd mapping opt dbg (IncrementalSession.incremental n1)))).map (fun c => c.payload) := by
    rw [hSortRel, List.map_map]
    rfl
  have hNormEq :
      normalizedArchivePayload (compilePipeline src cwd mapping plan opt dbg (IncrementalSession.incremental n1)).arArchive =
      normalizedArchivePayload (compilePipeline src cwd mapping plan opt dbg (IncrementalSession.incremental n2)).arArchive := by
    unfold normalizedArchivePayload compilePipeline assembleArtifacts
    simp only [List.map_map]
    have h1 : (fun x : CompiledCgu => x.payload) = (Prod.snd ∘ fun c : CompiledCgu => (canonicalArHeader c.memberFileName, c.payload)) := rfl
    rw [← h1, hPayloadsEq]
    have hr :
        (RmetaArtifact.mk src.crateName
          (src.modules.map (fun m => updateForCrateMetadata (toRealFileName mapping cwd m.relFile)))
          (mirInlineEnabled opt (IncrementalSession.incremental n1)) true) =
        (RmetaArtifact.mk src.crateName
          (src.modules.map (fun m => updateForCrateMetadata (toRealFileName mapping cwd m.relFile)))
          (mirInlineEnabled opt (IncrementalSession.incremental n2)) true) := by
      unfold mirInlineEnabled
      cases opt <;> rfl
    rw [hr]
  have hElfEq :
      (compilePipeline src cwd mapping plan opt dbg (IncrementalSession.incremental n1)).elf =
      (compilePipeline src cwd mapping plan opt dbg (IncrementalSession.incremental n2)).elf := by
    unfold compilePipeline assembleArtifacts
    dsimp only
    rw [hPayloadsEq]
  have hArchNeq :
      (compilePipeline src cwd mapping plan opt dbg (IncrementalSession.incremental n1)).arArchive ≠
      (compilePipeline src cwd mapping plan opt dbg (IncrementalSession.incremental n2)).arArchive := by
    intro hEq
    have hStrtabEq :
        (sortCgus (plan.map (compileOneCgu cwd mapping opt dbg (IncrementalSession.incremental n1)))).map (fun c => c.memberFileName) =
        (sortCgus (plan.map (compileOneCgu cwd mapping opt dbg (IncrementalSession.incremental n2)))).map (fun c => c.memberFileName) :=
      congrArg ArArchive.gnuStrtab hEq
    rw [hSortRel, List.map_map] at hStrtabEq
    -- Since `plan = firstItem :: restItems`, `sortCgus` of `plan.map ...` is non-empty!
    have hNonEmpty : ∀ (a : CompiledCgu) (as : List CompiledCgu),
        ∃ h t, insertCgu a as = h :: t := by
      intro a as
      cases as with
      | nil => exact ⟨a, [], rfl⟩
      | cons b bs =>
        unfold insertCgu
        cases lexLt a.cguName b.cguName with
        | true => exact ⟨a, b :: bs, rfl⟩
        | false => exact ⟨b, insertCgu a bs, rfl⟩
    let s1 := sortCgus (plan.map (compileOneCgu cwd mapping opt dbg (IncrementalSession.incremental n1)))
    have hS1Cons : ∃ h t, s1 = h :: t := by
      dsimp only [s1, plan, List.map, sortCgus]
      exact hNonEmpty _ _
    rcases hS1Cons with ⟨hd, tl, hEqCons⟩
    -- Note that every element of `s1` came from `plan.map (compileOneCgu ... n1)`, so its
    -- `memberFileName = makeMemberName hd.cguName (incremental n1)`.
    have hMemS1 : MemList hd (plan.map (compileOneCgu cwd mapping opt dbg (IncrementalSession.incremental n1))) := by
      -- Prove `MemList x (sortCgus xs) → MemList x xs`
      have hMemInsert : ∀ (z a : CompiledCgu) (as : List CompiledCgu),
          MemList z (insertCgu a as) → z = a ∨ MemList z as := by
        intro z a as
        induction as with
        | nil =>
          intro hm
          cases hm with
          | head _ => exact Or.inl rfl
          | tail ht => cases ht
        | cons b bs ih =>
          intro hm
          unfold insertCgu at hm
          cases hlt : lexLt a.cguName b.cguName with
          | true =>
            rw [hlt] at hm
            cases hm with
            | head _ => exact Or.inl rfl
            | tail ht => exact Or.inr ht
          | false =>
            rw [hlt] at hm
            cases hm with
            | head _ => exact Or.inr (MemList.head bs)
            | tail ht =>
              match ih ht with
              | Or.inl hza => exact Or.inl hza
              | Or.inr hzbs => exact Or.inr (MemList.tail hzbs)
      have hMemSort : ∀ (z : CompiledCgu) (xs : List CompiledCgu),
          MemList z (sortCgus xs) → MemList z xs := by
        intro z xs
        induction xs with
        | nil => intro hm; exact hm
        | cons a as ih =>
          intro hm
          unfold sortCgus at hm
          match hMemInsert z a (sortCgus as) hm with
          | Or.inl hza => subst hza; exact MemList.head as
          | Or.inr hms => exact MemList.tail (ih hms)
      apply hMemSort hd
      change MemList hd s1
      rw [hEqCons]
      exact MemList.head tl
    have hHdForm : hd.memberFileName = makeMemberName hd.cguName (IncrementalSession.incremental n1) := by
      have hAllForm : ∀ (xs : List CguPlanItem) (c : CompiledCgu),
          MemList c (xs.map (compileOneCgu cwd mapping opt dbg (IncrementalSession.incremental n1))) →
          c.memberFileName = makeMemberName c.cguName (IncrementalSession.incremental n1) := by
        intro xs c hm
        induction xs with
        | nil => cases hm
        | cons p ps ih =>
          cases hm with
          | head _ => rfl
          | tail ht => exact ih ht
      exact hAllForm plan hd hMemS1
    change s1.map (fun c => c.memberFileName) = s1.map ((fun c => c.memberFileName) ∘ retag) at hStrtabEq
    rw [hEqCons] at hStrtabEq
    simp only [List.map, Function.comp] at hStrtabEq
    injection hStrtabEq with hHeadName _
    rw [hHdForm] at hHeadName
    exact hne (makeMemberName_injective_nonce hd.cguName n1 n2 hHeadName)
  exact ⟨hRmetaEq, hNormEq, hElfEq, hArchNeq⟩

/-! ## Section 7: DDC & Proof-Carrying Build-Cache Receipt Soundness -/

/-- Semantic meaning of an emitted binary (`ElfArtifact` → observable behavior predicate). -/
abbrev BehaviorPred := ElfArtifact → Prop

/-- A proof-carrying verification receipt binds an emitted ELF artifact to a verified
    specification predicate `spec`. -/
structure VerificationReceipt (spec : BehaviorPred) where
  attestedElf : ElfArtifact
  proof : spec attestedElf

/-- **Theorem 4a: Bit-Exact Artifact Receipt Reuse Soundness.**
    If a cached verification receipt attests `spec` for `b1.elf` and a fresh build `b2`
    produces a bit-exact `elf` (in particular, via Theorem 1 or Theorem 2), then `spec`
    holds for `b2.elf` with zero re-verification required. -/
theorem bit_exact_artifact_sound_receipt_reuse
    {spec : BehaviorPred}
    (r : VerificationReceipt spec)
    (b2 : BuildOutput)
    (hBitExact : r.attestedElf = b2.elf) :
    spec b2.elf := by
  rw [← hBitExact]
  exact r.proof

/-- **Theorem 4b: Diverse Double-Compiling (DDC) Equivalence Soundness.**
    Given a trusted reference compiler `compileRef` satisfying `spec` and an untrusted
    candidate compiler `compileCand`, if their emitted artifacts are bit-exact
    (`compileCand input = compileRef input`), then the untrusted candidate output
    inherits `spec` directly (closing Thompson-style compiler trojan gaps on that input). -/
theorem ddc_bit_exact_implies_semantic_equivalence
    {Input : Type} {spec : BehaviorPred}
    (compileRef compileCand : Input → BuildOutput)
    (hRefSound : ∀ i, spec (compileRef i).elf)
    (i : Input)
    (hDdcMatch : (compileCand i).elf = (compileRef i).elf) :
    spec (compileCand i).elf := by
  rw [hDdcMatch]
  exact hRefSound i

/-- **Theorem 4c: Normalized-Payload Cache Soundness Under Incremental Nonces.**
    Even when raw `.rlib` archive bytes differ due to incremental `invocation_temp` nonces,
    equality of `normalizedArchivePayload` implies identical `ElfArtifact`s, so a
    payload-normalized verification cache soundly reuses receipts across warm incremental runs. -/
theorem normalized_payload_match_implies_elf_eq
    (b1 b2 : BuildOutput)
    (h1 : b1 = assembleArtifacts b1.rmeta b1.objs)
    (h2 : b2 = assembleArtifacts b2.rmeta b2.objs)
    (hNorm : normalizedArchivePayload b1.arArchive = normalizedArchivePayload b2.arArchive) :
    b1.elf = b2.elf := by
  have hPay : b1.arArchive.objEntries.map Prod.snd = b2.arArchive.objEntries.map Prod.snd :=
    congrArg Prod.snd hNorm
  have hElf1 : b1.elf.linkedPayloads = b1.arArchive.objEntries.map Prod.snd := by
    conv => lhs; rw [h1]
    conv => rhs; rw [h1]
    unfold assembleArtifacts
    simp only [List.map_map]
    rfl
  have hElf2 : b2.elf.linkedPayloads = b2.arArchive.objEntries.map Prod.snd := by
    conv => lhs; rw [h2]
    conv => rhs; rw [h2]
    unfold assembleArtifacts
    simp only [List.map_map]
    rfl
  cases b1 with
  | mk r1 o1 a1 e1 =>
    cases e1 with
    | mk p1 =>
      cases b2 with
      | mk r2 o2 a2 e2 =>
        cases e2 with
        | mk p2 =>
          dsimp only at hElf1 hElf2 hPay
          have hp : p1 = p2 := Eq.trans hElf1 (Eq.trans hPay hElf2.symm)
          exact congrArg ElfArtifact.mk hp

/-! ## Section 8: Constructive Counterexamples -/

private noncomputable def segWork     : List Nat := [119, 111, 114, 107] -- "work"
private noncomputable def segAlpha    : List Nat := [100, 105, 114, 95, 97, 108, 112, 104, 97] -- "dir_alpha"
private noncomputable def segBeta     : List Nat := [100, 105, 114, 95, 98, 101, 116, 97] -- "dir_beta"
private noncomputable def segRepro    : List Nat := [114, 101, 112, 114, 111] -- "repro"
private noncomputable def segLibRs    : List Nat := [108, 105, 98, 46, 114, 115] -- "lib.rs"

private noncomputable def sampleMod : SourceModule :=
  { relFile := [segLibRs]
    modId := 0
    usesTrackCaller := true
    hasInlineableHelper := true }

private noncomputable def sampleSrc : SourceTree :=
  { crateName := segRepro
    modules := [sampleMod] }

private noncomputable def samplePlan : List CguPlanItem :=
  [{ baseName := [99, 103, 117, 46, 48], mod := sampleMod }]

private noncomputable def emptyMapping : FilePathMapping :=
  { rules := [], scope := RemapScope.none }

/-- **Counterexample 1 (`ce1_unremapped_track_caller_breaks_cross_dir_repro`):**
    Even at `-C debuginfo=0`, omitting `--remap-path-prefix` causes `#[track_caller]`
    `Location::file()` to embed the raw checkout directory (`dir_alpha` vs `dir_beta`)
    into `.rodata`, breaking cross-directory bit-exactness of `.o`, `.rlib`, AND linked ELF. -/
theorem ce1_unremapped_track_caller_breaks_cross_dir_repro :
    let cwdAlpha : PathSegs := [segWork, segAlpha]
    let cwdBeta  : PathSegs := [segWork, segBeta]
    let bAlpha := compilePipeline sampleSrc cwdAlpha emptyMapping samplePlan OptLevel.o2 DebugInfoLevel.d0 IncrementalSession.clean
    let bBeta  := compilePipeline sampleSrc cwdBeta  emptyMapping samplePlan OptLevel.o2 DebugInfoLevel.d0 IncrementalSession.clean
    bAlpha.rmeta ≠ bBeta.rmeta ∧
    bAlpha.arArchive ≠ bBeta.arArchive ∧
    bAlpha.elf ≠ bBeta.elf := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h

/-- **Counterexample 2 (`ce2_incremental_session_suffix_breaks_raw_rlib_hash_match`):**
    Under `-C incremental` with complete `--remap-path-prefix`, two runs with distinct
    7-char base-36 `invocation_temp` suffixes (`"09w14lc"` vs `"1s0llzm"`) produce
    bit-identical `rmeta` and linked `elf`, yet strictly unequal raw `.rlib` archives. -/
theorem ce2_incremental_session_suffix_breaks_raw_rlib_hash_match :
    let cwd : PathSegs := [segWork, segAlpha]
    let vroot : PathSegs := [segRepro]
    let m : FilePathMapping := { rules := [{ fromPrefix := cwd, toPrefix := vroot }], scope := RemapScope.all }
    let n1 : List Nat := [48, 57, 119, 49, 52, 108, 99] -- "09w14lc"
    let n2 : List Nat := [49, 115, 48, 108, 108, 122, 109] -- "1s0llzm"
    let bCold := compilePipeline sampleSrc cwd m samplePlan OptLevel.o2 DebugInfoLevel.d0 (IncrementalSession.incremental n1)
    let bWarm := compilePipeline sampleSrc cwd m samplePlan OptLevel.o2 DebugInfoLevel.d0 (IncrementalSession.incremental n2)
    bCold.rmeta = bWarm.rmeta ∧
    bCold.elf = bWarm.elf ∧
    bCold.arArchive ≠ bWarm.arArchive := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  cases h

/-- **Counterexample 3 (`ce3_incremental_inline_suppression_changes_object_code_bytes`):**
    At `-C opt-level=2`, enabling `-C incremental` suppresses MIR `Inline`
    (`rustc_mir_transform/src/inline.rs`), altering the emitted object payload `codeTag`
    and linked ELF bytes relative to a clean `-C opt-level=2` build even in the exact same directory. -/
theorem ce3_incremental_inline_suppression_changes_object_code_bytes :
    let cwd : PathSegs := [segWork, segAlpha]
    let vroot : PathSegs := [segRepro]
    let m : FilePathMapping := { rules := [{ fromPrefix := cwd, toPrefix := vroot }], scope := RemapScope.all }
    let n1 : List Nat := [48, 57, 119, 49, 52, 108, 99]
    let bClean := compilePipeline sampleSrc cwd m samplePlan OptLevel.o2 DebugInfoLevel.d0 IncrementalSession.clean
    let bIncr  := compilePipeline sampleSrc cwd m samplePlan OptLevel.o2 DebugInfoLevel.d0 (IncrementalSession.incremental n1)
    bClean.rmeta ≠ bIncr.rmeta ∧
    bClean.elf ≠ bIncr.elf ∧
    bClean.arArchive ≠ bIncr.arArchive := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h

/-- **Counterexample 4 (`ce4_partial_object_scope_leaks_local_path_in_rmeta`):**
    Passing `--remap-path-scope=object` (instead of default `all`) produces bit-exact
    `.o` / `elf` across `dir_alpha` and `dir_beta`, YET `RealFileName::update_for_crate_metadata`
    preserves `localPart` because `scopes ≠ all ∧ scopes ≠ none`, breaking `.rmeta` and `.rlib`
    cross-directory bit-exactness. -/
theorem ce4_partial_object_scope_leaks_local_path_in_rmeta :
    let cwdAlpha : PathSegs := [segWork, segAlpha]
    let cwdBeta  : PathSegs := [segWork, segBeta]
    let vroot : PathSegs := [segRepro]
    let mAlpha : FilePathMapping := { rules := [{ fromPrefix := cwdAlpha, toPrefix := vroot }], scope := RemapScope.objectOnly }
    let mBeta  : FilePathMapping := { rules := [{ fromPrefix := cwdBeta,  toPrefix := vroot }], scope := RemapScope.objectOnly }
    let bAlpha := compilePipeline sampleSrc cwdAlpha mAlpha samplePlan OptLevel.o2 DebugInfoLevel.d2 IncrementalSession.clean
    let bBeta  := compilePipeline sampleSrc cwdBeta  mBeta  samplePlan OptLevel.o2 DebugInfoLevel.d2 IncrementalSession.clean
    bAlpha.elf = bBeta.elf ∧
    bAlpha.rmeta ≠ bBeta.rmeta ∧
    bAlpha.arArchive ≠ bBeta.arArchive := by
  refine ⟨rfl, ?_, ?_⟩
  · intro h; cases h
  · intro h; cases h

end ReproducibleBuildDeterminism
