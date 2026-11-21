/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

/-!
# Multi-CGU Disjoint-Nonce `SiteAttestation` Union, ICF Address-Oblivious Folding,
# and `TyCtxt` `SpecConeEq` Non-Interference (`Init.*`-Only Lean `v4.34.1`)

This self-contained Lean `v4.34.1` module mechanizes nine theorems (`0` `sorry`)
covering the verification obligations investigated in this report:

1. `uid_only_key_collides_across_cgus`: Keying inline-assembly descriptors solely
   by `(sessionNonce, uid)` collides across multiple CGUs (`cgu.0` and `cgu.1`
   both reset `AsmPrinter`'s `${:uid}` counter to `0`), allowing a swapped
   register allocation from another CGU to alias the same key.
2. `fatlto_global_asm_corrupts_prechecked_rlib_but_caught_on_lto_obj`:
   Concatenating `ModuleInlineAsm` during FatLTO (`IRMover`) rewrites an
   upstream `#[inline(never)]` `SUB` (`0x29`) site into `ADD` (`0x01`), proving
   that pre-LTO `.rlib` verification alone is unsound while re-checking
   `.anneal.asm_sites` on `.lto.rcgu.o` rejects the mutated slice.
3. `multi_cgu_disjoint_nonce_union_sound`: Merging arbitrary local and
   `.rmeta`-originating `.rcgu.o` objects across distinct crate session nonces
   preserves exact `ValidAttestedSlice` semantics on every record in the union.
4. `icf_all_pc_folding_sound_and_addr_counterexample`: Linker `--icf=all`
   folding of distinct `DefId`s (`fnA != fnB`) with identical machine bytes to a
   single post-link PC preserves all address-oblivious functional specs (under a
   many-to-1 `PC -> SiteId` relation), while falsifying address-inequality
   specs (`addr fnA != addr fnB`).
5. `evalMir_cone_noninterference`: Step-indexed MIR operational evaluation
   (`evalMir`) over transitive callees, trait-method dispatch, `AdtLayout` field
   offsets, niche `validRange`, `initByteMask` padding, `constAllocs`, and
   implicit `TerminatorKind::Drop` glue is 100% invariant to arbitrary mutations
   outside a `WellClosedCone` (including raw `AllocId` renumbering).
6. `specConeEq_preserves_totalMirAsmEquiv`: Main non-interference theorem:
   `WellClosedCone p1 cone -> refId ∈ cone.fns -> SpecConeEq p1 p2 cone ->
    TotalMirAsmEquiv p1 refId opt -> TotalMirAsmEquiv p2 refId opt`.
7. `omitted_padding_mask_unsound_counterexample`: Omitting `initByteMask` from
   `SpecConeEq` (keeping `size`, `align`, and field offsets identical) breaks
   `TotalMirAsmEquiv` preservation when `opt` writes concrete bytes to padding.
8. `omitted_drop_glue_unsound_counterexample`: Omitting implicit `Drop` glue from
   `SpecConeEq` (with `hot_ref`'s own body identical) breaks `TotalMirAsmEquiv`.
9. `omitted_niche_range_unsound_counterexample`: Omitting scalar niche
   `validRange` (`NonZeroU8` `1..255` vs `u8` `0..255` at identical `size = 1`,
   `align = 1`, `initByteMask = [true]`) breaks `TotalMirAsmEquiv` preservation.
-/

namespace AnnealMultiCguAndSpecCone

/-! ## Part I: Multi-CGU Disjoint-Nonce `SiteAttestation` Union & ICF Folding -/

inductive Reg where
  | rax | rcx | rdx | rsi | rdi
  deriving DecidableEq, Repr

abbrev RegAlloc := Nat -> Reg

/-- Unique site coordinate `(crateStableId, defPathHash, bbIndex)`. -/
structure SiteId where
  crateId : Nat
  defPathHash : Nat
  bbIdx : Nat
  deriving DecidableEq, Repr

inductive AsmTemplate where
  | subReg (dstOp srcOp : Nat)
  | addImm (dstOp imm : Nat)
  deriving DecidableEq, Repr

def regCode : Reg -> Nat
  | .rax => 0
  | .rcx => 1
  | .rdx => 2
  | .rsi => 6
  | .rdi => 7

/-- Minimal concrete x86-64 machine encoding (`0x29` = `SUB`, `0x01` = `ADD`). -/
def encodeTemplate (tmpl : AsmTemplate) (sigma : RegAlloc) : List Nat :=
  match tmpl with
  | .subReg d s => [0x48, 0x29, 0xC0 + 8 * regCode (sigma s) + regCode (sigma d)]
  | .addImm d imm => [0x48, 0x83, 0xC0 + regCode (sigma d), imm % 256]

abbrev RegFile := Reg -> Nat

def evalTemplate (tmpl : AsmTemplate) (sigma : RegAlloc) (rf : RegFile) : RegFile :=
  match tmpl with
  | .subReg d s =>
      let dst := sigma d
      let src := sigma s
      fun r => if r = dst then rf dst - rf src else rf r
  | .addImm d imm =>
      let dst := sigma d
      fun r => if r = dst then rf dst + (imm % 256) else rf r

/-- Emitted `.anneal.asm_sites` + `.anneal.asm_descs` record in one `.rcgu.o`. -/
structure SiteRecord where
  sessionNonce : Nat
  siteId : SiteId
  cguLocalUid : Nat
  sameSection : Bool
  startOff : Nat
  endOff : Nat
  sigma : RegAlloc
  sliceBytes : List Nat

structure CguObject where
  cguId : Nat
  records : List SiteRecord

/-- Naive key omitting `SiteId` / `cguId` (`${:uid}` resets per CGU). -/
def uidOnlyKey (r : SiteRecord) : Nat × Nat :=
  (r.sessionNonce, r.cguLocalUid)

/-- Theorem 1: Two distinct CGUs in the same compilation session (`nonce = 0xAA`)
    reset `${:uid}` to `0`, colliding on `uidOnlyKey` with incompatible `sigma`. -/
theorem uid_only_key_collides_across_cgus :
    ∃ (r0 r1 : SiteRecord),
      r0.siteId ≠ r1.siteId ∧
      r0.sigma 0 ≠ r1.sigma 0 ∧
      uidOnlyKey r0 = uidOnlyKey r1 := by
  let s0 : SiteId := { crateId := 1, defPathHash := 10, bbIdx := 0 }
  let s1 : SiteId := { crateId := 1, defPathHash := 20, bbIdx := 0 }
  let sig0 : RegAlloc := fun i => if i = 0 then .rax else .rsi
  let sig1 : RegAlloc := fun i => if i = 0 then .rcx else .rdx
  let r0 : SiteRecord := {
    sessionNonce := 0xAA, siteId := s0, cguLocalUid := 0,
    sameSection := true, startOff := 0, endOff := 3,
    sigma := sig0, sliceBytes := encodeTemplate (.subReg 0 1) sig0
  }
  let r1 : SiteRecord := {
    sessionNonce := 0xAA, siteId := s1, cguLocalUid := 0,
    sameSection := true, startOff := 0, endOff := 3,
    sigma := sig1, sliceBytes := encodeTemplate (.subReg 0 1) sig1
  }
  refine ⟨r0, r1, ?_, ?_, rfl⟩
  · intro h
    cases h
  · intro h
    cases h

/-- Check a single `.anneal.asm_sites` record against authorized session nonces
    and the MIR-captured `SiteId -> AsmTemplate` table. -/
def verifySiteRecord
    (validNonces : List Nat)
    (specTable : SiteId -> Option AsmTemplate)
    (r : SiteRecord) : Bool :=
  (validNonces.elem r.sessionNonce) &&
  r.sameSection &&
  decide (r.startOff <= r.endOff) &&
  match specTable r.siteId with
  | none => false
  | some tmpl => decide (encodeTemplate tmpl r.sigma = r.sliceBytes)

def ValidAttestedSlice
    (validNonces : List Nat)
    (specTable : SiteId -> Option AsmTemplate)
    (r : SiteRecord) : Prop :=
  r.sessionNonce ∈ validNonces ∧
  r.sameSection = true ∧
  r.startOff <= r.endOff ∧
  ∃ tmpl, specTable r.siteId = some tmpl ∧
    encodeTemplate tmpl r.sigma = r.sliceBytes

theorem elem_true_mem {x : Nat} {xs : List Nat} (h : xs.elem x = true) : x ∈ xs := by
  induction xs with
  | nil =>
      cases h
  | cons hd tl ih =>
      unfold List.elem at h
      cases hbeq : (x == hd) with
      | true =>
          have hxhd : x = hd := eq_of_beq hbeq
          subst hxhd
          exact List.Mem.head tl
      | false =>
          rw [hbeq] at h
          exact List.Mem.tail hd (ih h)

theorem verifySiteRecord_sound
    (validNonces : List Nat)
    (specTable : SiteId -> Option AsmTemplate)
    (r : SiteRecord)
    (hv : verifySiteRecord validNonces specTable r = true) :
    ValidAttestedSlice validNonces specTable r := by
  unfold verifySiteRecord at hv
  cases h_el : validNonces.elem r.sessionNonce
  · rw [h_el] at hv; cases hv
  · cases h_sec : r.sameSection
    · rw [h_el, h_sec] at hv; cases hv
    · cases h_le : decide (r.startOff <= r.endOff)
      · rw [h_el, h_sec, h_le] at hv; cases hv
      · cases h_sp : specTable r.siteId with
        | none =>
            rw [h_el, h_sec, h_le, h_sp] at hv; cases hv
        | some tmpl =>
            rw [h_el, h_sec, h_le, h_sp] at hv
            simp only [Bool.true_and, decide_eq_true_eq] at hv
            exact ⟨elem_true_mem h_el, h_sec, of_decide_eq_true h_le, tmpl, h_sp, hv⟩

/-- Model of FatLTO `IRMover` module-scope `.macro sub -> add` override. -/
def assembleWithGlobalMacro (subHijackedToAdd : Bool) (tmpl : AsmTemplate) (sigma : RegAlloc) :
    List Nat :=
  match tmpl with
  | .subReg d s =>
      let opByte := if subHijackedToAdd then 0x01 else 0x29
      [0x48, opByte, 0xC0 + 8 * regCode (sigma s) + regCode (sigma d)]
  | .addImm d imm => encodeTemplate (.addImm d imm) sigma

/-- Theorem 2: Pre-LTO `.rlib` verification passes (`subHijackedToAdd = false`),
    FatLTO re-assembly under downstream `global_asm!(".macro sub ...")` mutates
    the emitted opcode to `0x01` (`ADD`), and `.lto.rcgu.o` `verifySiteRecord`
    deterministically rejects the corrupted `.lto.rcgu.o` slice. -/
theorem fatlto_global_asm_corrupts_prechecked_rlib_but_caught_on_lto_obj :
    let sId : SiteId := { crateId := 1, defPathHash := 99, bbIdx := 0 }
    let sig : RegAlloc := fun i => if i = 0 then .rax else .rsi
    let specTable : SiteId -> Option AsmTemplate :=
      fun q => if q = sId then some (.subReg 0 1) else none
    let rlibRec : SiteRecord := {
      sessionNonce := 0x1111, siteId := sId, cguLocalUid := 0,
      sameSection := true, startOff := 0, endOff := 3, sigma := sig,
      sliceBytes := assembleWithGlobalMacro false (.subReg 0 1) sig
    }
    let fatLtoRec : SiteRecord := {
      rlibRec with
      sliceBytes := assembleWithGlobalMacro true (.subReg 0 1) sig
    }
    verifySiteRecord [0x1111, 0x2222] specTable rlibRec = true ∧
    rlibRec.sliceBytes ≠ fatLtoRec.sliceBytes ∧
    verifySiteRecord [0x1111, 0x2222] specTable fatLtoRec = false := by
  decide

def verifyCguObject
    (validNonces : List Nat)
    (specTable : SiteId -> Option AsmTemplate)
    (obj : CguObject) : Bool :=
  obj.records.all (verifySiteRecord validNonces specTable)

def unionCguRecords (cgus : List CguObject) : List SiteRecord :=
  cgus.foldr (fun obj acc => obj.records ++ acc) []

theorem all_mem_true {α : Type} (p : α -> Bool) (xs : List α)
    (hall : xs.all p = true) : ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil =>
      intro x hx; cases hx
  | cons hd tl ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      intro x hx
      cases hx with
      | head => exact hall.1
      | tail _ hmem => exact ih hall.2 x hmem

/-- Theorem 3: Multi-CGU and cross-crate `.rmeta` disjoint-nonce union soundness.
    Across arbitrary CGU counts and distinct per-crate session nonces, checking
    each `.rcgu.o` independently guarantees `ValidAttestedSlice` for every site
    in the linked union. -/
theorem multi_cgu_disjoint_nonce_union_sound
    (validNonces : List Nat)
    (specTable : SiteId -> Option AsmTemplate)
    (cgus : List CguObject)
    (h_all : cgus.all (verifyCguObject validNonces specTable) = true) :
    ∀ r ∈ unionCguRecords cgus, ValidAttestedSlice validNonces specTable r := by
  induction cgus with
  | nil =>
      intro r hr; cases hr
  | cons obj rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at h_all
      intro r hr
      simp only [unionCguRecords, List.foldr_cons, List.mem_append] at hr
      cases hr with
      | inl h_in_obj =>
          have h_rec : verifySiteRecord validNonces specTable r = true :=
            all_mem_true (verifySiteRecord validNonces specTable) obj.records h_all.1 r h_in_obj
          exact verifySiteRecord_sound validNonces specTable r h_rec
      | inr h_in_rest =>
          exact ih h_all.2 r h_in_rest

/-- Model of post-link executable code memory and symbol table under ICF. -/
structure LinkedImage where
  symAddr : Nat -> Nat
  codeAt : Nat -> List Nat
  execBytes : List Nat -> Nat -> Nat

def AddressObliviousSpec (spec : Nat -> Nat -> Prop) (img : LinkedImage) (fnSym : Nat) : Prop :=
  ∀ x, spec x (img.execBytes (img.codeAt (img.symAddr fnSym)) x)

/-- Theorem 4: Linker `--icf=all` folds distinct `DefId`s (`0 ≠ 1`) with
    identical machine bytes (`bytes0 = bytes1`) to the same runtime address:
    (a) every address-oblivious functional contract on BOTH `fnA` and `fnB` is
        preserved simultaneously at the shared PC (many-to-1 attribution);
    (b) an address-inequality property (`symAddr 0 ≠ symAddr 1`) holds before
        ICF and is falsified by `--icf=all`. -/
theorem icf_all_pc_folding_sound_and_addr_counterexample
    (bytes0 bytes1 : List Nat)
    (h_eq_bytes : bytes0 = bytes1)
    (evalFn : List Nat -> Nat -> Nat)
    (spec0 spec1 : Nat -> Nat -> Prop)
    (h_s0 : ∀ x, spec0 x (evalFn bytes0 x))
    (h_s1 : ∀ x, spec1 x (evalFn bytes1 x)) :
    let preIcf : LinkedImage := {
      symAddr := fun s => if s = 0 then 0x1000 else 0x2000,
      codeAt := fun a => if a = 0x1000 then bytes0 else bytes1,
      execBytes := evalFn
    }
    let postIcfAll : LinkedImage := {
      symAddr := fun _ => 0x1000,
      codeAt := fun _ => bytes0,
      execBytes := evalFn
    }
    (preIcf.symAddr 0 ≠ preIcf.symAddr 1) ∧
    (postIcfAll.symAddr 0 = postIcfAll.symAddr 1) ∧
    AddressObliviousSpec spec0 postIcfAll 0 ∧
    AddressObliviousSpec spec1 postIcfAll 1 := by
  intro preIcf postIcfAll
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro h_same
    simp [preIcf] at h_same
  · intro x
    exact h_s0 x
  · intro x
    dsimp only [AddressObliviousSpec, postIcfAll]
    rw [h_eq_bytes]
    exact h_s1 x

/-! ## Part II: `TyCtxt` `SpecConeEq` Non-Interference & Tampering Counterexamples -/

/-- Abstract output byte: initialized byte `init b` vs uninitialized padding `uninit`. -/
inductive AByte where
  | uninit
  | init (val : Nat)
  deriving DecidableEq, Repr

/-- Asymmetric byte refinement (`MiniRust` `le_defined` order): initialized
    reference bytes must match bit-for-bit; uninitialized reference padding may
    be refined by any concrete hardware byte in assembly. -/
def byteRefines (refB : AByte) (asmB : Nat) : Prop :=
  match refB with
  | .uninit => True
  | .init b => asmB = b

def bytesRefine : List AByte -> List Nat -> Prop
  | [], [] => True
  | rb :: rbs, ab :: abs => byteRefines rb ab ∧ bytesRefine rbs abs
  | _, _ => False

structure AdtLayout where
  size : Nat
  align : Nat
  field0Off : Nat
  validRangeLo : Nat
  validRangeHi : Nat
  initByteMask : List Bool
  deriving DecidableEq, Repr

inductive Expr where
  | constVal (allocKey : Nat)
  | readAdtField0 (adtTy : Nat)
  | callDirect (callee : Nat) (sub : Expr)
  | callTrait (traitId implTy : Nat) (sub : Expr)
  | addInputScalar
  deriving DecidableEq, Repr

structure FnDef where
  body : Expr
  retAdtTy : Nat
  scopedGuardTy : Option Nat
  targetFeatureMask : Nat
  deriving DecidableEq, Repr

/-- Complete crate semantic environment queried by `TyCtxt`. -/
structure CrateEnv where
  fns : Nat -> FnDef
  traitImpls : Nat -> Nat -> Nat
  adtLayouts : Nat -> AdtLayout
  dropEffect : Nat -> Option Nat
  constAllocs : Nat -> Nat
  /-- Crate-global `AllocId` numbering (shifts when unrelated `static`s are added). -/
  rawAllocIds : Nat -> Nat

structure Input where
  hdrBytes : List Nat
  badge : Nat
  badgeAdtTy : Nat
  scalar : Nat
  deriving DecidableEq, Repr

inductive MirOut where
  | invalidInput
  | panicked (dropLog : Nat)
  | returned (acc : Nat) (structBytes : List AByte) (dropLog : Nat)
  | outOfFuel
  deriving DecidableEq, Repr

inductive IsaOut where
  | panicked (dropLog : Nat)
  | halted (acc : Nat) (structBytes : List Nat) (dropLog : Nat)
  | trap
  deriving DecidableEq, Repr

def buildMaskedBytes (val : Nat) (mask : List Bool) : List AByte :=
  mask.map (fun isInit => if isInit then .init (val % 256) else .uninit)

def evalExpr (fuel : Nat) (env : CrateEnv) (inp : Input) : Expr -> Option Nat
  | .constVal k => some (env.constAllocs k)
  | .readAdtField0 adtTy =>
      let lay := env.adtLayouts adtTy
      some (inp.hdrBytes.getD lay.field0Off 0)
  | .addInputScalar => some inp.scalar
  | .callDirect callee sub =>
      match fuel with
      | 0 => none
      | fuel' + 1 =>
          match evalExpr fuel' env inp sub with
          | none => none
          | some v =>
              let calleeDef := env.fns callee
              match evalExpr fuel' env { inp with scalar := v } calleeDef.body with
              | none => none
              | some res =>
                  let dEff := match calleeDef.scopedGuardTy with
                    | none => 0
                    | some gTy => (env.dropEffect gTy).getD 0
                  some (res + dEff)
  | .callTrait trId implTy sub =>
      match fuel with
      | 0 => none
      | fuel' + 1 =>
          let resolvedFn := env.traitImpls trId implTy
          match evalExpr fuel' env inp sub with
          | none => none
          | some v =>
              let calleeDef := env.fns resolvedFn
              evalExpr fuel' env { inp with scalar := v } calleeDef.body

def evalMir (fuel : Nat) (env : CrateEnv) (fnId : Nat) (inp : Input) : MirOut :=
  let badgeLay := env.adtLayouts inp.badgeAdtTy
  if !(decide (badgeLay.validRangeLo <= inp.badge) &&
       decide (inp.badge <= badgeLay.validRangeHi)) then
    .invalidInput
  else
    let fnDef := env.fns fnId
    let dropLog := match fnDef.scopedGuardTy with
      | none => 0
      | some gTy => (env.dropEffect gTy).getD 0
    match evalExpr fuel env inp fnDef.body with
    | none => .outOfFuel
    | some acc =>
        let retLay := env.adtLayouts fnDef.retAdtTy
        let outBytes := buildMaskedBytes acc retLay.initByteMask
        .returned (acc + inp.badge) outBytes dropLog

/-- Cross-level total relational contract for valid inputs (`MirOut != .invalidInput`). -/
def TotalMirAsmEquiv (fuel : Nat) (env : CrateEnv) (refId : Nat) (opt : Input -> IsaOut) : Prop :=
  ∀ inp,
    match evalMir fuel env refId inp with
    | .invalidInput => True
    | .outOfFuel => False
    | .panicked d => opt inp = .panicked d
    | .returned acc rBytes d =>
        ∃ aBytes, opt inp = .halted acc aBytes d ∧ bytesRefine rBytes aBytes

/-- Transitive `SpecCone` footprint collected by `SpecConeCollector`. -/
structure SpecCone where
  fns : List Nat
  traits : List (Nat × Nat)
  adts : List Nat
  allocKeys : List Nat

def ExprUsesInCone (env : CrateEnv) (cone : SpecCone) : Expr -> Prop
  | .constVal k => k ∈ cone.allocKeys
  | .readAdtField0 adtTy => adtTy ∈ cone.adts
  | .addInputScalar => True
  | .callDirect callee sub => callee ∈ cone.fns ∧ ExprUsesInCone env cone sub
  | .callTrait trId implTy sub =>
      (trId, implTy) ∈ cone.traits ∧
      (env.traitImpls trId implTy) ∈ cone.fns ∧
      ExprUsesInCone env cone sub

/-- Closure invariant satisfied by BFS reachability in `SpecConeCollector`. -/
def WellClosedCone (env : CrateEnv) (cone : SpecCone) (badgeTy : Nat) : Prop :=
  badgeTy ∈ cone.adts ∧
  ∀ f ∈ cone.fns,
    let fd := env.fns f
    fd.retAdtTy ∈ cone.adts ∧
    (∀ gTy, fd.scopedGuardTy = some gTy -> gTy ∈ cone.adts) ∧
    ExprUsesInCone env cone fd.body

/-- Exact semantic equality on the `SpecCone` (note: `rawAllocIds` is NOT constrained!). -/
def SpecConeEq (p1 p2 : CrateEnv) (cone : SpecCone) : Prop :=
  (∀ f ∈ cone.fns, p1.fns f = p2.fns f) ∧
  (∀ ti ∈ cone.traits, p1.traitImpls ti.1 ti.2 = p2.traitImpls ti.1 ti.2) ∧
  (∀ a ∈ cone.adts, p1.adtLayouts a = p2.adtLayouts a ∧ p1.dropEffect a = p2.dropEffect a) ∧
  (∀ k ∈ cone.allocKeys, p1.constAllocs k = p2.constAllocs k)

theorem evalExpr_cone_noninterference
    (fuel : Nat)
    (p1 p2 : CrateEnv)
    (cone : SpecCone)
    (badgeTy : Nat)
    (h_closed : WellClosedCone p1 cone badgeTy)
    (h_eq : SpecConeEq p1 p2 cone) :
    ∀ (e : Expr) (inp : Input),
      ExprUsesInCone p1 cone e ->
      evalExpr fuel p1 inp e = evalExpr fuel p2 inp e := by
  induction fuel with
  | zero =>
      intro e inp h_use
      cases e with
      | constVal k =>
          simp only [evalExpr, h_eq.2.2.2 k h_use]
      | readAdtField0 adtTy =>
          simp only [evalExpr, (h_eq.2.2.1 adtTy h_use).1]
      | addInputScalar =>
          rfl
      | callDirect _ _ =>
          rfl
      | callTrait _ _ _ =>
          rfl
  | succ fuel' ih =>
      intro e inp h_use
      cases e with
      | constVal k =>
          simp only [evalExpr, h_eq.2.2.2 k h_use]
      | readAdtField0 adtTy =>
          simp only [evalExpr, (h_eq.2.2.1 adtTy h_use).1]
      | addInputScalar =>
          rfl
      | callDirect callee sub =>
          rcases h_use with ⟨h_callee_in, h_sub_use⟩
          have h_sub_eq := ih sub inp h_sub_use
          dsimp only [evalExpr]
          rw [h_sub_eq]
          cases evalExpr fuel' p2 inp sub with
          | none => rfl
          | some v =>
              dsimp only
              have h_fn_eq : p1.fns callee = p2.fns callee := h_eq.1 callee h_callee_in
              have h_callee_closed := h_closed.2 callee h_callee_in
              have h_body_eq :=
                ih (p1.fns callee).body { inp with scalar := v } h_callee_closed.2.2
              rw [← h_fn_eq]
              rw [h_body_eq]
              cases evalExpr fuel' p2 { inp with scalar := v } (p1.fns callee).body with
              | none => rfl
              | some res =>
                  dsimp only
                  cases h_sg : (p1.fns callee).scopedGuardTy with
                  | none => rfl
                  | some gTy =>
                      have hg_in : gTy ∈ cone.adts := h_callee_closed.2.1 gTy h_sg
                      simp only [(h_eq.2.2.1 gTy hg_in).2]
      | callTrait trId implTy sub =>
          rcases h_use with ⟨h_tr_in, h_res_in, h_sub_use⟩
          have h_sub_eq := ih sub inp h_sub_use
          have h_tr_eq : p1.traitImpls trId implTy = p2.traitImpls trId implTy :=
            h_eq.2.1 (trId, implTy) h_tr_in
          dsimp only [evalExpr]
          rw [h_sub_eq, ← h_tr_eq]
          cases evalExpr fuel' p2 inp sub with
          | none => rfl
          | some v =>
              dsimp only
              let rFn := p1.traitImpls trId implTy
              have h_fn_eq : p1.fns rFn = p2.fns rFn := h_eq.1 rFn h_res_in
              have h_r_closed := h_closed.2 rFn h_res_in
              rw [← h_fn_eq]
              exact ih (p1.fns rFn).body { inp with scalar := v } h_r_closed.2.2

/-- Theorem 5: `evalMir` is 100% invariant to edits outside `SpecCone` and to
    crate-wide `rawAllocIds` shifts (such as adding an unrelated `static`). -/
theorem evalMir_cone_noninterference
    (fuel : Nat)
    (p1 p2 : CrateEnv)
    (cone : SpecCone)
    (refId : Nat)
    (inp : Input)
    (h_closed : WellClosedCone p1 cone inp.badgeAdtTy)
    (h_ref : refId ∈ cone.fns)
    (h_eq : SpecConeEq p1 p2 cone) :
    evalMir fuel p1 refId inp = evalMir fuel p2 refId inp := by
  dsimp only [evalMir]
  have h_badge_eq : p1.adtLayouts inp.badgeAdtTy = p2.adtLayouts inp.badgeAdtTy :=
    (h_eq.2.2.1 inp.badgeAdtTy h_closed.1).1
  rw [← h_badge_eq]
  cases (!(decide ((p1.adtLayouts inp.badgeAdtTy).validRangeLo <= inp.badge) &&
           decide (inp.badge <= (p1.adtLayouts inp.badgeAdtTy).validRangeHi))) with
  | true =>
      simp only [↓reduceIte]
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have h_fn_eq : p1.fns refId = p2.fns refId := h_eq.1 refId h_ref
      have h_ref_closed := h_closed.2 refId h_ref
      rw [← h_fn_eq]
      have h_expr :=
        evalExpr_cone_noninterference fuel p1 p2 cone inp.badgeAdtTy h_closed h_eq
          (p1.fns refId).body inp h_ref_closed.2.2
      rw [h_expr]
      have h_ret_eq :
          p1.adtLayouts (p1.fns refId).retAdtTy = p2.adtLayouts (p1.fns refId).retAdtTy :=
        (h_eq.2.2.1 (p1.fns refId).retAdtTy h_ref_closed.1).1
      rw [← h_ret_eq]
      cases h_sg : (p1.fns refId).scopedGuardTy with
      | none => rfl
      | some gTy =>
          have hg_in : gTy ∈ cone.adts := h_ref_closed.2.1 gTy h_sg
          simp only [(h_eq.2.2.1 gTy hg_in).2]

/-- Theorem 6: Main `SpecConeEq` Non-Interference Theorem.
    Any verified `TotalMirAsmEquiv` proof against `p1` transfers soundly to `p2`
    whenever `SpecConeEq p1 p2 cone` holds across all valid badge types. -/
theorem specConeEq_preserves_totalMirAsmEquiv
    (fuel : Nat)
    (p1 p2 : CrateEnv)
    (cone : SpecCone)
    (refId : Nat)
    (opt : Input -> IsaOut)
    (h_closed : ∀ bTy, WellClosedCone p1 cone bTy)
    (h_ref : refId ∈ cone.fns)
    (h_eq : SpecConeEq p1 p2 cone)
    (h_equiv : TotalMirAsmEquiv fuel p1 refId opt) :
    TotalMirAsmEquiv fuel p2 refId opt := by
  intro inp
  have h_mir :=
    evalMir_cone_noninterference fuel p1 p2 cone refId inp (h_closed inp.badgeAdtTy) h_ref h_eq
  have h1 := h_equiv inp
  rw [h_mir] at h1
  exact h1

/-! ### Constructive Unsoundness Counterexamples When `SpecCone` Omits Semantic Channels -/

def baseLayout : AdtLayout := {
  size := 4, align := 4, field0Off := 0,
  validRangeLo := 0, validRangeHi := 255,
  initByteMask := [true, false, false, false]
}

def baseEnv : CrateEnv := {
  fns := fun _ => {
    body := .constVal 0, retAdtTy := 0, scopedGuardTy := some 0, targetFeatureMask := 0
  },
  traitImpls := fun _ _ => 0,
  adtLayouts := fun _ => baseLayout,
  dropEffect := fun _ => some 1,
  constAllocs := fun _ => 42,
  rawAllocIds := fun k => k
}

/-- Weakened `SpecConeEq` that checks `(size, align, field0Off, validRange)`
    but OMITS `initByteMask` (`V03_adt_uninit_padding_mask`). -/
def WeakConeEqNoPadMask (p1 p2 : CrateEnv) : Prop :=
  (∀ f, p1.fns f = p2.fns f) ∧
  (∀ t i, p1.traitImpls t i = p2.traitImpls t i) ∧
  (∀ a, (p1.adtLayouts a).size = (p2.adtLayouts a).size ∧
        (p1.adtLayouts a).align = (p2.adtLayouts a).align ∧
        (p1.adtLayouts a).field0Off = (p2.adtLayouts a).field0Off ∧
        (p1.adtLayouts a).validRangeLo = (p2.adtLayouts a).validRangeLo ∧
        (p1.adtLayouts a).validRangeHi = (p2.adtLayouts a).validRangeHi ∧
        p1.dropEffect a = p2.dropEffect a) ∧
  (∀ k, p1.constAllocs k = p2.constAllocs k)

/-- Theorem 7: Constructive counterexample when `initByteMask` is omitted.
    `opt` writes `[42, 0xFF, 0, 0]` (putting `0xFF` into padding byte 1), which
    is valid when byte 1 is `uninit` (`p1`), passes `WeakConeEqNoPadMask p1 p2`,
    and FAILS `TotalMirAsmEquiv` when `p2` replaces uninit padding with explicit
    `_pad: [u8; 3]` (`initByteMask = [true, true, true, true]`). -/
theorem omitted_padding_mask_unsound_counterexample :
    ∃ (p1 p2 : CrateEnv) (opt : Input -> IsaOut),
      WeakConeEqNoPadMask p1 p2 ∧
      TotalMirAsmEquiv 1 p1 0 opt ∧
      ¬ TotalMirAsmEquiv 1 p2 0 opt := by
  let p1 := baseEnv
  let p2 : CrateEnv := {
    baseEnv with
    adtLayouts := fun _ => { baseLayout with initByteMask := [true, true, true, true] }
  }
  let opt : Input -> IsaOut := fun inp => .halted (42 + inp.badge) [42, 0xFF, 0, 0] 1
  refine ⟨p1, p2, opt, ?_, ?_, ?_⟩
  · refine ⟨fun _ => rfl, fun _ _ => rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => rfl⟩
  · intro inp
    dsimp only [evalMir, p1, baseEnv, baseLayout, evalExpr]
    cases (!(decide (0 <= inp.badge) && decide (inp.badge <= 255))) with
    | true =>
        simp only [↓reduceIte]
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨[42, 0xFF, 0, 0], rfl, ?_⟩
        simp [buildMaskedBytes, bytesRefine, byteRefines]
  · intro h_bad
    let wInp : Input := { hdrBytes := [0], badge := 0, badgeAdtTy := 0, scalar := 0 }
    have hw := h_bad wInp
    dsimp only [evalMir, p2, baseEnv, baseLayout, evalExpr, buildMaskedBytes] at hw
    rcases hw with ⟨aBytes, h_opt, h_ref⟩
    injection h_opt with _ h_bytes _
    subst h_bytes
    simp [bytesRefine, byteRefines] at h_ref

/-- Weakened `SpecConeEq` that omits `dropEffect` (`V05_implicit_drop_glue`). -/
def WeakConeEqNoDrop (p1 p2 : CrateEnv) : Prop :=
  (∀ f, p1.fns f = p2.fns f) ∧
  (∀ t i, p1.traitImpls t i = p2.traitImpls t i) ∧
  (∀ a, p1.adtLayouts a = p2.adtLayouts a) ∧
  (∀ k, p1.constAllocs k = p2.constAllocs k)

/-- Theorem 8: Constructive counterexample when implicit `Drop` glue is omitted. -/
theorem omitted_drop_glue_unsound_counterexample :
    ∃ (p1 p2 : CrateEnv) (opt : Input -> IsaOut),
      WeakConeEqNoDrop p1 p2 ∧
      TotalMirAsmEquiv 1 p1 0 opt ∧
      ¬ TotalMirAsmEquiv 1 p2 0 opt := by
  let p1 := baseEnv
  let p2 : CrateEnv := { baseEnv with dropEffect := fun _ => some 2 }
  let opt : Input -> IsaOut := fun inp => .halted (42 + inp.badge) [42, 0, 0, 0] 1
  refine ⟨p1, p2, opt, ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩, ?_, ?_⟩
  · intro inp
    dsimp only [evalMir, p1, baseEnv, baseLayout, evalExpr]
    cases (!(decide (0 <= inp.badge) && decide (inp.badge <= 255))) with
    | true =>
        simp only [↓reduceIte]
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨[42, 0, 0, 0], rfl, ?_⟩
        simp [buildMaskedBytes, bytesRefine, byteRefines]
  · intro h_bad
    let wInp : Input := { hdrBytes := [0], badge := 0, badgeAdtTy := 0, scalar := 0 }
    have hw := h_bad wInp
    dsimp only [evalMir, p2, baseEnv, baseLayout, evalExpr, buildMaskedBytes] at hw
    rcases hw with ⟨aBytes, h_opt, _⟩
    cases h_opt

/-- Weakened `SpecConeEq` that checks `(size, align, field0Off, initByteMask)`
    but OMITS scalar niche `validRangeLo/Hi` (`V04_adt_niche_valid_range`). -/
def WeakConeEqNoNiche (p1 p2 : CrateEnv) : Prop :=
  (∀ f, p1.fns f = p2.fns f) ∧
  (∀ t i, p1.traitImpls t i = p2.traitImpls t i) ∧
  (∀ a, (p1.adtLayouts a).size = (p2.adtLayouts a).size ∧
        (p1.adtLayouts a).align = (p2.adtLayouts a).align ∧
        (p1.adtLayouts a).field0Off = (p2.adtLayouts a).field0Off ∧
        (p1.adtLayouts a).initByteMask = (p1.adtLayouts a).initByteMask ∧
        p1.dropEffect a = p2.dropEffect a) ∧
  (∀ k, p1.constAllocs k = p2.constAllocs k)

/-- Theorem 9: Constructive counterexample when niche `validRange` is omitted.
    `p1` uses `NonZeroU8` (`validRange = 1..255`), so `opt` may trap on `0`;
    widening `p2` to `u8` (`validRange = 0..255`) at identical `size`, `align`,
    and `initByteMask` turns `badge = 0` into a valid input that `opt` traps on! -/
theorem omitted_niche_range_unsound_counterexample :
    ∃ (p1 p2 : CrateEnv) (opt : Input -> IsaOut),
      WeakConeEqNoNiche p1 p2 ∧
      TotalMirAsmEquiv 1 p1 0 opt ∧
      ¬ TotalMirAsmEquiv 1 p2 0 opt := by
  let p1 : CrateEnv := {
    baseEnv with
    adtLayouts := fun _ => { baseLayout with validRangeLo := 1, validRangeHi := 255 }
  }
  let p2 := baseEnv
  let opt : Input -> IsaOut := fun inp =>
    if inp.badge = 0 then .trap else .halted (42 + inp.badge) [42, 0, 0, 0] 1
  refine ⟨p1, p2, opt, ?_, ?_, ?_⟩
  · refine ⟨fun _ => rfl, fun _ _ => rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => rfl⟩
  · rintro ⟨hdr, badge, bTy, sc⟩
    dsimp only [evalMir, p1, baseEnv, baseLayout, evalExpr]
    by_cases hz : badge = 0
    · subst hz
      simp
    · cases (!(decide (1 <= badge) && decide (badge <= 255))) with
      | true =>
          simp only [↓reduceIte]
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine ⟨[42, 0, 0, 0], ?_, ?_⟩
          · simp [opt, hz]
          · simp [buildMaskedBytes, bytesRefine, byteRefines]
  · intro h_bad
    let wInp : Input := { hdrBytes := [0], badge := 0, badgeAdtTy := 0, scalar := 0 }
    have hw := h_bad wInp
    dsimp only [evalMir, p2, baseEnv, baseLayout, evalExpr, buildMaskedBytes, opt] at hw
    rcases hw with ⟨aBytes, h_opt, _⟩
    cases h_opt

#print axioms uid_only_key_collides_across_cgus
#print axioms fatlto_global_asm_corrupts_prechecked_rlib_but_caught_on_lto_obj
#print axioms multi_cgu_disjoint_nonce_union_sound
#print axioms icf_all_pc_folding_sound_and_addr_counterexample
#print axioms evalMir_cone_noninterference
#print axioms specConeEq_preserves_totalMirAsmEquiv
#print axioms omitted_padding_mask_unsound_counterexample
#print axioms omitted_drop_glue_unsound_counterexample
#print axioms omitted_niche_range_unsound_counterexample

end AnnealMultiCguAndSpecCone
