/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Required
import ZeroedAudit
import NativeProviderAudit
open Lean Elab Command

/-!
This is the final compiled audit of the connection from Rust annotations to
Lean proofs. It compares three sources of evidence: the source/extraction
binding manifest, the actual compiled raw types and specifications, and the
configured proof and required-check modules. Each comparison is closed: both
missing and unexpected owners are errors. Every present annotation requires its
corresponding compiled specification and proof. Removing an annotation removes
that claim; reviewers must assess that visible change in the Rust diff.

After checking ownership and arbitrary-outcome adequacy, the audit records the
proof dependency graph and checks the axioms used by every audited declaration.
The graph reports what the compiled proofs use; it does not prescribe their
structure. External ABI size and alignment inputs are permitted only with their
data signatures and explicit read interpretations, rather than as axioms about
useful layout properties.
-/

private def checkUnemittedNativeType (env : Environment) (row : Json) : TermElabM Unit := do
  let .ok rust := row.getObjValAs? String "rust"
    | throwError "Unemitted native type must name its Rust owner"
  let .ok ident := row.getObjValAs? Nat "def_id"
    | throwError "Unemitted native type must name its compiler identity"
  unless (row.getObjVal? "raw").toOption == some Json.null &&
      row.getObjValAs? Nat "parameters" == .ok 0 do
    throwError "Unemitted native type has a malformed disposition: {rust}"
  let .ok expectedRaw := row.getObjValAs? String "expected_raw"
    | throwError "Unemitted native type must record its derived raw name"
  let derived := "Zerocopy." ++ String.intercalate "." ((rust.drop "zerocopy::".length).toString.splitOn "::")
  unless rust.startsWith "zerocopy::" && expectedRaw == derived &&
      !env.constants.toList.any (fun entry => expectedRaw.toName.isPrefixOf entry.1) do
    throwError "Unemitted native type changed its Rust identity or has a compiled raw declaration: {rust}"
  let nativeText ← IO.FS.readFile "Zerocopy/translation.json"
  let .ok native := Json.parse nativeText | throwError "Invalid native type emission evidence"
  let .ok emitted := native.getObjValAs? (Array Json) "types"
    | throwError "Native type emission evidence must contain its complete type inventory"
  if emitted.any (fun entry => entry.getObjValAs? Nat "def_id" == .ok ident ||
      entry.getObjValAs? String "rust_name" == .ok rust) then
    throwError "Unemitted native type still has a producer binding: {rust}"
  let expectedName := toJson (rust.splitOn "::" |>.map fun part =>
    Json.mkObj [("Ident", toJson #[toJson part, toJson (0 : Nat)])])
  for (key, filename) in #[ ("native", "zerocopy.llbc"), ("original", "zerocopy.before.ullbc") ] do
    let .ok evidence := row.getObjVal? key | throwError "Unemitted native type lacks its {key} declaration"
    let contents ← IO.FS.readFile filename
    let .ok parsed := Json.parse contents | throwError "Invalid native type extraction snapshot"
    let .ok crate := parsed.getObjVal? "translated" | throwError "Missing native type extraction snapshot"
    let .ok declarations := crate.getObjValAs? (Array Json) "type_decls"
      | throwError "Missing native type declaration inventory"
    let selected := declarations.filter (fun entry => entry.getObjValAs? Nat "def_id" == .ok ident)
    unless selected.size == 1 && selected[0]! == evidence do
      throwError "Unemitted native type differs from its {key} compiler declaration: {rust}"
    unless (evidence.getObjVal? "kind").toOption == some (Json.mkObj [("Enum", Json.arr #[])]) do
      throwError "Unemitted native type must be a zero-case enum: {rust}"
    let .ok ownership := evidence.getObjVal? "item_meta" | throwError "Unemitted native type lacks compiler ownership"
    unless (ownership.getObjVal? "name").toOption == some expectedName &&
        ownership.getObjValAs? Bool "is_local" == .ok true &&
        ownership.getObjValAs? Bool "started_from" == .ok false do
      throwError "Unemitted native type changed its source ownership: {rust}"
    let .ok generics := evidence.getObjVal? "generics" | throwError "Unemitted native type lacks original generics"
    for field in #["regions", "types", "const_generics", "trait_clauses", "trait_type_constraints",
        "regions_outlive", "types_outlive"] do
      unless (generics.getObjValAs? (Array Json) field).toOption == some #[] do
        throwError "Unemitted native type has unsupported generic obligations: {rust}"

-- This closed boundary adds an interpretation-only provider to the std
-- primitive. Compare whole definitions independently of the functional proofs,
-- then bind each reached native call (including unannotated helpers) to its
-- original Rust endpoints and exact canonical provider.
private partial def stdTransmuteCalls (expression : Expr) : Array Expr :=
  if expression.getAppFn.isConstOf `core.intrinsics.transmute then
    #[expression] ++ expression.getAppArgs.foldl
      (fun found arg => found ++ stdTransmuteCalls arg) #[]
  else
    match expression with
    | .app fn arg => stdTransmuteCalls fn ++ stdTransmuteCalls arg
    | .lam _ ty body _ | .forallE _ ty body _ => stdTransmuteCalls ty ++ stdTransmuteCalls body
    | .letE _ ty value body _ => stdTransmuteCalls ty ++ stdTransmuteCalls value ++ stdTransmuteCalls body
    | .mdata _ body | .proj _ _ body => stdTransmuteCalls body
    | _ => #[]

private def auditStdTransmute (bindings : Json) : TermElabM Unit := do
  let env ← getEnv
  unless env.contains `core.intrinsics.transmute do return
  let ctor ← Term.elabType (← `(∀ (Src Dst : Type),
    (Src → Aeneas.Std.Result Dst) → Zerocopy.StdOwnedTransmute Src Dst))
  let some (.ctorInfo classCtor) := env.find? `Zerocopy.StdOwnedTransmute.mk
    | throwError "Standard transmute provider must retain its reviewed one-field carrier"
  unless ← Meta.isDefEq classCtor.type ctor do
    throwError "Standard transmute provider carrier changed"
  let expectedType ← Term.elabType (← `(∀ {Src : Type} (Dst : Type)
    [Zerocopy.StdOwnedTransmute Src Dst], Src → Aeneas.Std.Result Dst))
  let expectedBody ← Term.elabTerm (← `(fun {Src : Type} (Dst : Type)
    [provider : Zerocopy.StdOwnedTransmute Src Dst] (src : Src) => provider.run src)) none
  Term.synthesizeSyntheticMVarsNoPostponing
  let some (.defnInfo primitive) := env.find? `core.intrinsics.transmute
    | throwError "Standard transmute interpretation must be a definition"
  unless (← Meta.isDefEq primitive.type expectedType) &&
      (← Meta.isDefEq primitive.value (← instantiateMVars expectedBody)) do
    throwError "Standard transmute extended signature or whole interpretation changed"
  let forward ← Term.elabTerm (← `(
    ({ run := fun value => Aeneas.Std.Result.ok (Aeneas.Std.core.num.U32.to_le_bytes value) } :
      Zerocopy.StdOwnedTransmute Aeneas.Std.U32 (Aeneas.Std.Array Aeneas.Std.U8 4#usize)))) none
  let backward ← Term.elabTerm (← `(
    ({ run := fun bytes => Aeneas.Std.Result.ok (Aeneas.Std.core.num.U32.from_le_bytes bytes) } :
      Zerocopy.StdOwnedTransmute (Aeneas.Std.Array Aeneas.Std.U8 4#usize) Aeneas.Std.U32))) none
  let boolean ← Term.elabTerm (← `(
    ({ run := fun byte => if byte.val < 2 then Aeneas.Std.Result.ok (decide (byte.val = 1))
        else Aeneas.Std.Result.fail Aeneas.Std.Error.undef } :
      Zerocopy.StdOwnedTransmute Aeneas.Std.U8 Bool))) none
  Term.synthesizeSyntheticMVarsNoPostponing
  for (providerName, providerValue) in #[(`Zerocopy.stdTransmuteU32ToBytes, forward),
      (`Zerocopy.stdTransmuteBytesToU32, backward), (`Zerocopy.stdTransmuteU8ToBool, boolean)] do
    let some (.defnInfo provider) := env.find? providerName
      | throwError "Standard transmute provider {providerName} must be a definition"
    unless ← Meta.isDefEq provider.value (← instantiateMVars providerValue) do
      throwError "Standard transmute provider {providerName} changed its whole interpretation"
  let .ok admission := bindings.getObjVal? "admission"
    | throwError "Standard transmute requires original compiler admission"
  let .ok stages := admission.getObjVal? "stages"
    | throwError "Standard transmute requires both compiler admission stages"
  let .ok original := stages.getObjVal? "before"
    | throwError "Standard transmute lacks original admission"
  let .ok lowered := stages.getObjVal? "llbc"
    | throwError "Standard transmute lacks lowered admission"
  let .ok originalCalls := original.getObjValAs? (Array Json) "calls"
    | throwError "Standard transmute lacks original call evidence"
  let .ok loweredCalls := lowered.getObjValAs? (Array Json) "calls"
    | throwError "Standard transmute lacks lowered call evidence"
  let originalStd := originalCalls.filter fun row => row.getObjValAs? String "callee" == .ok "core::intrinsics::transmute"
  let loweredStd := loweredCalls.filter fun row => row.getObjValAs? String "callee" == .ok "core::intrinsics::transmute"
  -- Ordered type arguments identify source and destination independently;
  -- preserve each call, its owner, and its multiplicity through lowering.
  unless originalStd == loweredStd do
    throwError "Standard transmute changed original ordered Rust endpoints or call ownership"
  let .ok executions := lowered.getObjValAs? (Array Json) "executions"
    | throwError "Standard transmute lacks the complete execution closure"
  let nativeText ← IO.FS.readFile "Zerocopy/translation.json"
  let .ok native := Json.parse nativeText | throwError "Invalid native primitive call map"
  let .ok functions := native.getObjValAs? (Array Json) "functions"
    | throwError "Missing native primitive function map"
  for execution in executions do
    if execution.getObjValAs? String "origin" != .ok "body" then continue
    let .ok rust := execution.getObjValAs? String "rust" | throwError "Missing primitive call owner"
    let expected := loweredStd.filter fun row => row.getObjValAs? String "caller" == .ok rust
    let selected := functions.filter fun row => row.getObjValAs? String "rust_name" == .ok rust
    -- General dictionary owners can have a different native spelling. Owners
    -- with this boundary must have an exact producer identity from their call.
    if expected.isEmpty && selected.isEmpty then continue
    let candidates := if expected.isEmpty then selected else functions.filter fun row =>
      expected.any (fun call => call.getObjValAs? Nat "caller_def_id" == row.getObjValAs? Nat "def_id")
    unless !candidates.isEmpty do throwError "Missing compiled standard transmute owner {rust}"
    -- Native loop splitting can emit several bodies for one Rust owner. Audit
    -- their aggregate inventory rather than silently omitting the loop helper.
    let mut actual : Array Expr := #[]
    let mut names : Array Name := #[]
    for candidate in candidates do
      let .ok raw := candidate.getObjValAs? String "lean_name" | throwError "Missing native owner name"
      unless !names.contains raw.toName do throwError "Repeated native primitive owner {raw}"
      names := names.push raw.toName
      let some (.defnInfo owner) := env.find? raw.toName
        | throwError "Reached primitive owner {rust} must retain its compiled body"
      actual := actual ++ stdTransmuteCalls owner.value
    unless actual.size == expected.size do
      throwError "Compiled standard transmute call inventory differs for {rust}"
    -- Consume one original witness per compiled call. Repeated calls with the
    -- same endpoints are legal, but neither omission nor duplication is legal.
    let mut remaining := expected
    for call in actual do
      let args := call.getAppArgs
      unless args.size == 4 do throwError "Standard transmute acquired unsupported compiled arguments"
      let matching ← remaining.filterM fun row => do
        let .ok types := row.getObjValAs? (Array String) "type_arguments" | throwError "Missing Rust endpoints"
        let (source, target, canonical) ← match types.toList with
          | ["u32", "[u8;4]"] => pure ((← Term.elabType (← `(Aeneas.Std.U32))),
              (← Term.elabType (← `(Aeneas.Std.Array Aeneas.Std.U8 4#usize))), `Zerocopy.stdTransmuteU32ToBytes)
          | ["[u8;4]", "u32"] => pure ((← Term.elabType (← `(Aeneas.Std.Array Aeneas.Std.U8 4#usize))),
              (← Term.elabType (← `(Aeneas.Std.U32))), `Zerocopy.stdTransmuteBytesToU32)
          | ["u8", "bool"] => pure ((← Term.elabType (← `(Aeneas.Std.U8))),
              (← Term.elabType (← `(Bool))), `Zerocopy.stdTransmuteU8ToBool)
          | _ => throwError "Unsupported original Rust standard transmute endpoints"
        unless row.getObjValAs? String "provider" == .ok canonical.toString do
          throwError "Original Rust endpoint provider binding changed"
        return (← Meta.isDefEq args[0]! source) && (← Meta.isDefEq args[1]! target) &&
          args[2]! == mkConst canonical
      unless !matching.isEmpty do
        throwError "Compiled standard transmute did not retain its canonical endpoint provider in {rust}"
      let some selectedIndex := remaining.findIdx? (· == matching[0]!)
        | throwError "Missing matched standard transmute call"
      remaining := remaining.extract 0 selectedIndex ++ remaining.extract (selectedIndex + 1) remaining.size

run_elab do
  let env ← getEnv
  let layoutInputs := #[`Zerocopy.RustLayout.size, `Zerocopy.RustLayout.alignInput]
  -- Generic alignment reads identify the ABI-capable model. Earlier models
  -- may have only the pointer-width size read and require no generic ABI inputs.
  let hasLayoutReads := env.contains `core.mem.align_of
  let modelInputs := if hasLayoutReads then layoutInputs else #[]
  -- ByteOrder carries formatting dictionaries even when a numerical method
  -- never formats a value. The backend leaves Formatter's representation
  -- abstract. Admit this exact opaque type, with no axiom about its values or
  -- behavior; changing it into a proposition or a function is an error.
  let opaqueCarriers := #[`Aeneas.Std.core.fmt.Formatter]
  let expectedCarrier ← Term.elabType (← `(Type))
  for carrier in opaqueCarriers do
    let some (.axiomInfo info) := env.find? carrier
      | throwError "Missing pinned opaque carrier {carrier}"
    unless info.levelParams.isEmpty && (← Meta.isDefEq info.type expectedCarrier) do
      throwError "Opaque carrier {carrier} changed its type-only signature"
  -- The interface audit below independently checks Ptr's exact data signature
  -- and all uncallable validator stubs before this axiom list is used.
  let opaqueCarriers := if env.contains `Zerocopy.pointer.ptr.def.Ptr then
    opaqueCarriers.push `Zerocopy.pointer.ptr.def.Ptr else opaqueCarriers
  -- ABI inputs are functions returning data, with no proposition asserting
  -- alignment, size, or correctness. A changed type could smuggle a theorem
  -- into the allowed axiom list, so check their exact compiled signatures.
  let expected ← Term.elabType (← `(Type → Aeneas.Std.Usize))
  for input in modelInputs do
    let some (.axiomInfo info) := env.find? input
      | throwError "Missing external layout input {input}"
    unless ← Meta.isDefEq info.type expected do
      throwError "External layout input {input} changed its data-only signature"
  if hasLayoutReads then
    -- The concrete byte case is part of the external primitive interpretation.
    -- Audit its whole definition independently, including the generic fallback;
    -- a true concrete trait law must not bless unrelated type alignments.
    let alignment ← Term.elabTerm (← `(
      fun (T : Type) => by
        classical
        exact if T = Aeneas.Std.U8 then 1#usize
          else Zerocopy.RustLayout.alignInput T)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    unless ← Meta.isDefEq (mkConst `Zerocopy.RustLayout.align) (← instantiateMVars alignment) do
      throwError "External alignment model changed its concrete or generic interpretation"
    -- Independently state each primitive interpretation. Keeping the data
    -- axioms while ignoring them must not silently shrink the modeled domain.
    let alignRead ← Term.elabTerm (← `(
      fun (T : Type) => Aeneas.Std.Result.ok (Zerocopy.RustLayout.align T))) none
    let sizeRead ← Term.elabTerm (← `(
      fun (T : Type) => by
        classical
        exact Aeneas.Std.Result.ok
          (if T = Aeneas.Std.Usize then
            ({ bv := BitVec.ofNat _ (System.Platform.numBits / 8) } : Aeneas.Std.Usize)
           else Zerocopy.RustLayout.size T))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let alignRead ← instantiateMVars alignRead
    let sizeRead ← instantiateMVars sizeRead
    unless ← Meta.isDefEq (mkConst `core.mem.align_of) alignRead do
      throwError "External alignment read changed its data-input interpretation"
    unless env.contains `core.mem.size_of do
      throwError "Missing external size read"
    unless ← Meta.isDefEq (mkConst `core.mem.size_of) sizeRead do
      throwError "External size read changed its data-input interpretation"
  if env.contains `util.transmute_unchecked then
    let expected ← Term.elabTerm (← `(fun {Src : Type} (Dst : Type) (src : Src) => by
      classical
      exact if hs : Src = Aeneas.Std.U8 then
        if hd : Dst = Bool then
          let byte := cast hs src
          if byte.val < 2 then Aeneas.Std.Result.ok (cast hd.symm (decide (byte.val = 1)))
          else Aeneas.Std.Result.fail Aeneas.Std.Error.undef
        else Aeneas.Std.Result.fail Aeneas.Std.Error.undef
      else Aeneas.Std.Result.fail Aeneas.Std.Error.undef)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    unless ← Meta.isDefEq (mkConst `util.transmute_unchecked) (← instantiateMVars expected) do
      throwError "External Boolean conversion changed its complete interpretation"
  if env.contains `util.copy_unchecked then
    let expected ← Term.elabTerm (← `(fun (src dst : Aeneas.Std.Slice Aeneas.Std.U8) =>
      if h : src.val.length ≤ dst.val.length then
        Aeneas.Std.Result.ok (Aeneas.Std.Slice.from
          (src.val ++ dst.val.drop src.val.length) (by
            have := dst.property
            simp only [List.length_append, List.length_drop]
            omega))
      else Aeneas.Std.Result.fail Aeneas.Std.Error.undef)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    unless ← Meta.isDefEq (mkConst `util.copy_unchecked) (← instantiateMVars expected) do
      throwError "External byte copy changed its complete interpretation"
  if env.contains `util.copy_unchecked_at then
    -- A write contract exercises only fitting calls. Check the complete leaf
    -- too: an out-of-range start panics, and a too-long copy is forbidden.
    let expected ← Term.elabTerm (← `(fun (src dst : Aeneas.Std.Slice Aeneas.Std.U8)
        (start : Aeneas.Std.Usize) =>
      if start.val ≤ dst.val.length then
        if h : src.val.length ≤ dst.val.length - start.val then
          Aeneas.Std.Result.ok (Aeneas.Std.Slice.from
            (dst.val.take start.val ++ src.val ++ dst.val.drop (start.val + src.val.length)) (by
              have := dst.property
              simp only [List.length_append, List.length_take, List.length_drop]
              omega))
        else Aeneas.Std.Result.fail Aeneas.Std.Error.undef
      else Aeneas.Std.Result.fail Aeneas.Std.Error.panic)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    unless ← Meta.isDefEq (mkConst `util.copy_unchecked_at) (← instantiateMVars expected) do
      throwError "External offset copy changed its complete guarded interpretation"
  if env.contains `util.validity.read_byte then
    let expected ← Term.elabTerm (← `(fun (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
        (index : Aeneas.Std.Usize) =>
      if index.val < bytes.val.length then Aeneas.Std.Result.ok bytes.val[index.val]!
      else Aeneas.Std.Result.fail Aeneas.Std.Error.panic)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    unless ← Meta.isDefEq (mkConst `util.validity.read_byte) (← instantiateMVars expected) do
      throwError "External candidate byte read changed its complete guarded interpretation"
  if env.contains `core.num.Usize.unchecked_add || env.contains `core.num.Usize.unchecked_mul then
    -- A proof on fitting inputs cannot distinguish UB from a recoverable
    -- panic outside that domain. Independently check both complete primitive
    -- interpretations, so changing only their failure tag still fails CI.
    let add ← Term.elabTerm (← `(fun (left right : Aeneas.Std.Usize) =>
      if left.val + right.val ≤ Aeneas.Std.Usize.max then left + right
      else Aeneas.Std.Result.fail Aeneas.Std.Error.undef)) none
    let mul ← Term.elabTerm (← `(fun (left right : Aeneas.Std.Usize) =>
      if left.val * right.val ≤ Aeneas.Std.Usize.max then left * right
      else Aeneas.Std.Result.fail Aeneas.Std.Error.undef)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    for (primitive, expected) in #[(`core.num.Usize.unchecked_add, add),
                              (`core.num.Usize.unchecked_mul, mul)] do
      unless env.contains primitive && (← Meta.isDefEq (mkConst primitive) (← instantiateMVars expected)) do
        throwError "External unchecked arithmetic changed its forbidden-execution interpretation: {primitive}"
  if env.contains `core.num.nonzero.NonZero.new_unchecked then
    -- A successful caller proves only its nonzero branch. Independently audit
    -- the complete leaf, including zero and unsupported native carriers.
    let expected ← Term.elabTerm (← `(fun {T Inner : Type}
        (_inst : Zerocopy.core.num.nonzero.ZeroablePrimitive T Inner) (x : T) => by
      classical
      exact if h : T = Aeneas.Std.Usize then
        if (cast h x : Aeneas.Std.Usize) = 0#usize then
          Aeneas.Std.Result.fail Aeneas.Std.Error.undef
        else Aeneas.Std.Result.ok (⟨x⟩ : core.num.nonzero.NonZero T Inner)
      else Aeneas.Std.Result.fail Aeneas.Std.Error.undef)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    unless ← Meta.isDefEq (mkConst `core.num.nonzero.NonZero.new_unchecked)
        (← instantiateMVars expected) do
      throwError "External NonZero::new_unchecked changed its complete forbidden-execution interpretation"
  -- Module indices identify declarations by compiled ownership. A matching
  -- namespace is insufficient: a generated or unrelated module could otherwise
  -- install a theorem under a handwritten proof's expected name.
  let mut proofModules : Array ModuleIdx := #[]
  for moduleName in proofModuleNames do
    let some index := env.getModuleIdx? moduleName
      | throwError "Proof module {moduleName} was not imported"
    proofModules := proofModules.push index
  let mut auditModules : Array ModuleIdx := #[]
  for moduleName in auditModuleNames do
    let some index := env.getModuleIdx? moduleName
      | throwError "Audit module {moduleName} was not imported"
    auditModules := auditModules.push index
  -- Compiled spec declarations determine coverage; there is no separately
  -- generated theorem roster that can omit a specification and its checks.
  let some specsModule := env.getModuleIdx? `Specs
    | throwError "Compiled inline specifications must be imported"
  let mut required : Array Name := #[]
  let mut actualModels : Array Name := #[]
  let mut actualFamilies : Array Name := #[]
  let mut expectedFamilies : Array Name := #[]
  for (declName, info) in env.constants.toList do
    if env.getModuleIdxFor? declName != some specsModule ||
        declName.getPrefix != `Zerocopy.Specs then continue
    let .defnInfo info := info
      | throwError "Unexpected inline specification declaration {declName}"
    -- The generated namespace contains specs and their outcome families only.
    -- Collect untagged definitions for an exact family comparison below, rather
    -- than treating every nearby declaration as an authored contract.
    if !AeneasSpecs.specAttribute.hasTag env declName then
      actualFamilies := actualFamilies.push declName
      continue
    unless info.type.consumeMData == mkSort Level.zero do
      throwError "Inline specification {declName} must be a proposition"
    let (modelName, _) ← AeneasSpecs.specBinding declName
    AeneasSpecs.checkSpecContract declName
    let familyName := AeneasSpecs.specContractName declName
    unless env.getModuleIdxFor? familyName == some specsModule do
      throwError "Abstract contract {familyName} must be declared with its inline specification"
    expectedFamilies := expectedFamilies.push familyName
    -- One Rust function owns one inline specification. Multiple specs could
    -- let the canonical theorem prove a weaker sibling of the intended claim.
    if actualModels.contains modelName then
      throwError "Compiled inline specifications repeat model {modelName}"
    actualModels := actualModels.push modelName
    required := required.push ((`Zerocopy.Proofs).str declName.getString!)
  let missingFamilies := expectedFamilies.filter (!actualFamilies.contains ·)
  let extraFamilies := actualFamilies.filter (!expectedFamilies.contains ·)
  unless missingFamilies.isEmpty && extraFamilies.isEmpty do
    throwError "Compiled abstract contracts disagree with inline specifications: missing {missingFamilies}; unexpected {extraFamilies}"
  if required.isEmpty then
    throwError "No compiled inline specifications were found"
  -- Reuse the model mapping already produced from Rust annotations/extraction.
  -- Deriving both Specs and Required from a smaller subset cannot hide a root.
  -- The manifest is an audited data input produced from source ownership and
  -- extraction. Validate its schema and mode before using any names/counts;
  -- a development manifest still must satisfy the same compiled binding checks.
  let bindingsText ← IO.FS.readFile "bindings.json"
  let .ok bindings := Json.parse bindingsText
    | throwError "Model bindings are not valid JSON"
  let .ok version := bindings.getObjValAs? Nat "version"
    | throwError "Model bindings must declare version 3"
  unless version == 3 do
    throwError "Model bindings must declare version 3"
  let .ok mode := bindings.getObjValAs? String "mode"
    | throwError "Model bindings must declare their validation mode"
  unless mode == "verified-live" || mode == "development" do
    throwError "Model bindings have an unsupported validation mode {mode}"
  let .ok entriesValue := bindings.getObjVal? "bindings"
    | throwError "Model bindings must contain their source/extraction binding table"
  let .ok entries := entriesValue.getObj?
    | throwError "Model bindings must contain a binding table object"
  if mode == "verified-live" then
    let .ok admission := bindings.getObjVal? "admission"
      | throwError "Missing mandatory execution admission evidence"
    let .ok admissionVersion := admission.getObjValAs? Nat "version"
      | throwError "Invalid execution admission evidence"
    unless admissionVersion == 1 do
      throwError "Unsupported execution admission evidence"
    let .ok stages := admission.getObjVal? "stages"
      | throwError "Missing execution admission stages"
    let rootNames := entries.toArray.filterMap fun pair =>
      if pair.2.getObjValAs? String "kind" == .ok "function" then some pair.1 else none
    for stage in #["before", "llbc"] do
      let .ok evidence := stages.getObjVal? stage
        | throwError "Missing {stage} execution admission stage"
      let .ok roots := evidence.getObjValAs? (Array String) "roots"
        | throwError "Invalid {stage} execution admission roots"
      unless roots.size == rootNames.size && rootNames.all roots.contains do
        throwError "Execution admission roots disagree with the function binding table"
  auditStdTransmute bindings
  auditZeroed bindings
  auditNativeProviders bindings
  let some typesModule := env.getModuleIdx? `Zerocopy.Types
    | throwError "Raw extracted types must be imported"
  let some shapesModule := env.getModuleIdx? `ModelShapes
    | throwError "ModelShapes must be imported from their generated module"
  let some modelsModule := env.getModuleIdx? `Models
    | throwError "Models must be imported from their generated module"
  let mut expectedTypes : Array Name := #[]
  let mut expectedLocalRust : Array String := #[]
  let mut expectedModels : Array Name := #[]
  let mut expectedDefaults : Array Name := #[]
  for (rustName, entry) in entries.toArray do
    let .ok kind := entry.getObjValAs? String "kind"
      | throwError "Binding for {rustName} must name its owner kind"
    let .ok raw := entry.getObjValAs? String "raw"
      | throwError "Binding for {rustName} must name its exact extracted carrier"
    let .ok generics := entry.getObjValAs? (Array String) "generics"
      | throwError "Binding for {rustName} must name its original type parameters"
    let rawName := raw.toName
    -- Function entries bind a source spec to the exact extracted constant and
    -- its complete type/value prefix. Type entries bind nominal raw ownership
    -- to shape and full-provider declarations in their generated modules.
    if kind == "function" then
      if expectedModels.contains rawName then
        throwError "Model bindings repeat model {rawName}"
      expectedModels := expectedModels.push rawName
      let .ok sourceSpec := entry.getObjValAs? String "spec"
        | throwError "Function binding for {rustName} must name its inline specification"
      let .ok sourceInputs := entry.getObjValAs? (Array String) "inputs"
        | throwError "Function binding for {rustName} must name its original value inputs"
      let specName := (`Zerocopy.Specs).str sourceSpec
      -- A provided method may lose its unused Self dictionary during lowering.
      -- The source/compiler binder records that exact bound; the compiled
      -- registry must add precisely that trait as a specification premise.
      let .ok erased := entry.getObjVal? "erased_self_bound"
        | throwError "Function binding must record its enclosing-bound disposition"
      let registeredDefault ← AeneasSpecs.defaultTraitBody? rawName
      if erased == Json.null then
        unless registeredDefault.isNone do
          throwError "Unexpected enclosing trait premise on {rawName}"
      else
        let .ok traitRust := erased.getObjValAs? String "rust"
          | throwError "Erased Self bound must name its original Rust trait"
        let .ok traitId := erased.getObjValAs? Nat "trait_def_id"
          | throwError "Erased Self bound must retain its compiler trait identity"
        let .ok arguments := erased.getObjValAs? (Array Json) "arguments"
          | throwError "Erased Self bound must retain its original type arguments"
        unless arguments == (Array.range generics.size).map
            (fun index => toJson #[toJson "parameter", toJson index]) do
          throwError "Unsupported enclosing trait instantiation on {rawName}"
        let .ok dictionaries := bindings.getObjValAs? (Array Json) "trait_dictionaries"
          | throwError "Missing native trait dictionary inventory"
        let owners := dictionaries.filter fun row =>
          row.getObjValAs? String "rust" == .ok traitRust &&
          row.getObjValAs? Nat "def_id" == .ok traitId
        unless owners.size == 1 do throwError "Erased Self bound lost its exact native owner"
        let .ok traitRaw := owners[0]!.getObjValAs? String "raw"
          | throwError "Missing enclosing trait's compiled dictionary"
        let some owner := registeredDefault
          | throwError "Missing compiled enclosing trait premise for {rawName}"
        unless owner.trait == traitRaw.toName && owner.parameterCount == arguments.size do
          throwError "Compiled enclosing trait premise changed its Rust owner on {rawName}"
        expectedDefaults := expectedDefaults.push rawName
      unless env.getModuleIdxFor? specName == some specsModule do
        throwError "Function binding for {rustName} does not name a compiled inline specification"
      let (boundModel, boundInputs) ← AeneasSpecs.specBinding specName
      -- This also rejects a same-arity call on replaced or reordered inputs:
      -- specBinding already checked each argument's original variable identity.
      let .ok dictionaryCount := entry.getObjValAs? Nat "dictionary_count"
        | throwError "Function binding for {rustName} must count its original trait dictionaries"
      let semanticCount ← Meta.forallTelescope (← getConstInfo rawName).type fun native _ => do
        let (_, models) ← AeneasSpecs.splitNativeModels native
        pure models.size
      unless boundModel == rawName &&
          boundInputs == generics.size + dictionaryCount + sourceInputs.size + semanticCount do
        throwError "Compiled specification {specName} changed its source model or original input prefix"
    else if kind == "type" then
      if expectedTypes.contains rawName then
        throwError "Type bindings repeat extracted carrier {rawName}"
      expectedTypes := expectedTypes.push rawName
      expectedLocalRust := expectedLocalRust.push rustName
      let some (.inductInfo rawInfo) := env.find? rawName
        | throwError "Type binding is not a raw nominal carrier: {rawName}"
      unless env.getModuleIdxFor? rawName == some typesModule &&
          rawInfo.numParams == generics.size do
        throwError "Raw nominal binding changed its ownership or type parameters: {rawName}"
      let (fields, mathType, decoder, provider, count) ← AeneasSpecs.modelBinding rawName
      unless count == generics.size do
        throwError "Mathematical model changed its original generic parameters: {rawName}"
      -- Compare independently emitted manifest names with the registry's actual
      -- declarations. Derived fixed names still need this external comparison;
      -- a correct provider for the wrong Rust owner is not an acceptable proof.
      for (key, actual) in #[("fields", fields), ("model", mathType),
          ("decoder", decoder), ("provider", provider)] do
        let .ok expected := entry.getObjValAs? String key
          | throwError "Type binding for {rustName} must name its {key}"
        unless actual == expected.toName do
          throwError "Compiled {key} {actual} disagrees with its Rust owner binding {expected}"
      -- Shapes can depend on mathematical child types before any decoder is
      -- built. Their ownership stays separate from full decoder/provider assembly.
      unless env.getModuleIdxFor? fields == some shapesModule &&
          env.getModuleIdxFor? mathType == some shapesModule do
        throwError "Mathematical fields and model must be owned by ModelShapes: {rawName}"
      unless env.getModuleIdxFor? decoder == some modelsModule &&
          env.getModuleIdxFor? provider == some modelsModule do
        throwError "Decoder and provider must be owned by Models: {rawName}"
      let .ok authored := entry.getObjValAs? Bool "authored"
        | throwError "Type binding must record its authored model disposition"
      -- An unannotated owner must receive its structural carrier, not an
      -- arbitrary smaller interpretation introduced by generation.
      unless authored || mathType == fields do
        throwError "Unannotated model must use its nominal Fields carrier: {rawName}"
    else
      throwError "Unsupported binding kind {kind} for {rustName}"
  let defaults ← AeneasSpecs.defaultTraitBodies
  unless defaults.size == expectedDefaults.size &&
      defaults.all (fun owner => expectedDefaults.contains owner.function) do
    throwError "Compiled enclosing trait premises disagree with source bindings"
  -- This image is classified from LLBC type and trait declarations in live
  -- mode. Every compiled raw inductive must belong to exactly one class;
  -- local nominals must also have the source-bound model/provider entry above.
  let .ok image := bindings.getObjValAs? (Array Json) "type_image"
    | throwError "Model bindings must contain the complete raw type image"
  let mut imageTypes : Array Name := #[]
  let mut imageLocalTypes : Array Name := #[]
  let mut imageLocalRust : Array String := #[]
  let mut imageRust : Array String := #[]
  for row in image do
    let .ok rust := row.getObjValAs? String "rust"
      | throwError "Raw type image entry must name its Rust identity"
    let .ok category := row.getObjValAs? String "category"
      | throwError "Raw type image entry must name its extraction category"
    let .ok parameterCount := row.getObjValAs? Nat "parameters"
      | throwError "Raw type image entry must name its generated parameter count"
    if category == "unemitted-uninhabited" then
      unless mode == "verified-live" && parameterCount == 0 &&
          (row.getObjVal? "raw").toOption == some Json.null && (entries.get? rust).isNone do
        throwError "Unemitted native type has a model claim or malformed disposition: {rust}"
      if imageRust.contains rust then
        throwError "Raw type image repeats unemitted Rust owner {rust}"
      imageRust := imageRust.push rust
      checkUnemittedNativeType env row
      continue
    let .ok raw := row.getObjValAs? String "raw"
      | throwError "Raw type image entry must name its generated carrier"
    unless category == "local-nominal" || category == "trait-dictionary" ||
        category == "external-nominal" do
      throwError "Unsupported raw type image category {category} for {rust}"
    let rawName := raw.toName
    if imageRust.contains rust || imageTypes.contains rawName then
      throwError "Raw type image repeats Rust identity or generated carrier {rust}: {rawName}"
    imageRust := imageRust.push rust
    imageTypes := imageTypes.push rawName
    let some (.inductInfo info) := env.find? rawName
      | throwError "Raw type image entry is not an inductive carrier: {rawName}"
    unless env.getModuleIdxFor? rawName == some typesModule && info.numParams == parameterCount do
      throwError "Raw type image changed its compiled module or parameter count: {rawName}"
    if category == "local-nominal" then
      let some bound := entries.get? rust
        | throwError "Local raw type image has no source binding: {rust}"
      let .ok boundRaw := bound.getObjValAs? String "raw"
        | throwError "Local raw type image has no bound generated carrier: {rust}"
      unless boundRaw == raw do
        throwError "Local raw type image disagrees with source-bound carrier: {rust}"
      imageLocalTypes := imageLocalTypes.push rawName
      imageLocalRust := imageLocalRust.push rust
  let missingLocalTypes := expectedTypes.filter (!imageLocalTypes.contains ·)
  let extraLocalTypes := imageLocalTypes.filter (!expectedTypes.contains ·)
  let missingLocalRust := expectedLocalRust.filter (!imageLocalRust.contains ·)
  let extraLocalRust := imageLocalRust.filter (!expectedLocalRust.contains ·)
  unless missingLocalTypes.isEmpty && extraLocalTypes.isEmpty &&
      missingLocalRust.isEmpty && extraLocalRust.isEmpty do
    throwError "Source-bound nominal models disagree with raw type image: missing {missingLocalTypes}; unexpected {extraLocalTypes}"
  let mut actualTypes : Array Name := #[]
  for (constName, constInfo) in env.constants.toList do
    if env.getModuleIdxFor? constName == some typesModule then
      if let .inductInfo _ := constInfo then
        actualTypes := actualTypes.push constName
  let missingTypes := actualTypes.filter (!imageTypes.contains ·)
  let extraTypes := imageTypes.filter (!actualTypes.contains ·)
  unless missingTypes.isEmpty && extraTypes.isEmpty do
    throwError "Compiled raw types disagree with classified extraction image: missing {missingTypes}; unexpected {extraTypes}"
  -- Trait registrations are a closed image, too. A missing registration must
  -- not make a computational dictionary look like an ordinary runtime value,
  -- and a law class must belong to the module generated from Rust annotations.
  let .ok dictionaries := bindings.getObjValAs? (Array Json) "trait_dictionaries"
    | throwError "Model bindings must contain their native trait dictionary image"
  let .ok laws := bindings.getObjValAs? (Array Json) "trait_laws"
    | throwError "Model bindings must contain their annotated trait laws"
  let .ok implementations := bindings.getObjValAs? (Array Json) "trait_impl_laws"
    | throwError "Model bindings must contain their required trait implementations"
  let some lawsModule := env.getModuleIdx? `TraitLaws
    | throwError "Trait laws must be imported from their generated module"
  -- Test modules have their own miniature dictionaries. Only the compiled
  -- extraction's carriers participate in the production binding comparison.
  let registered := (← AeneasSpecs.traitLawBindings).filter
    (fun entry => env.getModuleIdxFor? entry.raw == some typesModule)
  let mut expectedDictionaries : Array Name := #[]
  for row in dictionaries do
    let .ok raw := row.getObjValAs? String "raw"
      | throwError "Native trait dictionary must name its compiled carrier"
    let rawName := raw.toName
    if expectedDictionaries.contains rawName then
      throwError "Native trait dictionary image repeats {rawName}"
    expectedDictionaries := expectedDictionaries.push rawName
    unless registered.any (·.raw == rawName) do
      throwError "Native trait dictionary lacks its compiled registration: {rawName}"
    let some (.inductInfo _) := env.find? rawName
      | throwError "Native trait dictionary is not an inductive carrier: {rawName}"
    -- Generated dictionaries must be classified as such, rather than merely
    -- borrowing the name of a local data structure from the type image.
    if env.getModuleIdxFor? rawName == some typesModule then
      unless image.any (fun entry => entry.getObjValAs? String "raw" == .ok raw &&
          entry.getObjValAs? String "category" == .ok "trait-dictionary") do
        throwError "Native trait dictionary has the wrong raw image category: {rawName}"
  unless registered.size == expectedDictionaries.size &&
      registered.all (fun entry => expectedDictionaries.contains entry.raw) do
    throwError "Compiled trait dictionary registrations disagree with native bindings"
  let mut expectedLaws : Array Name := #[]
  for row in laws do
    let .ok raw := row.getObjValAs? String "raw"
      | throwError "Annotated trait must name its exact dictionary"
    let .ok law := row.getObjValAs? String "law"
      | throwError "Annotated trait must name its generated law class"
    let .ok count := row.getObjValAs? Nat "generic_count"
      | throwError "Annotated trait must count its original type parameters"
    let lawName := law.toName
    if expectedLaws.contains lawName then throwError "Repeated trait law {lawName}"
    expectedLaws := expectedLaws.push lawName
    unless registered.any (fun entry => entry.raw == raw.toName && entry.law == some lawName) do
      throwError "Compiled trait law disagrees with its exact Rust dictionary: {lawName}"
    let some (.inductInfo info) := env.find? lawName
      | throwError "Trait law is not a compiled class: {lawName}"
    let some registration := registered.find? (·.raw == raw.toName)
      | throwError "Missing exact trait law registration"
    AeneasSpecs.checkTraitLawModelParameters registration count
    unless env.getModuleIdxFor? lawName == some lawsModule &&
        info.numParams == count + 1 + registration.modelParameters.size &&
        (← Meta.forallTelescope info.type fun _ result => pure (result.consumeMData == mkSort .zero)) do
      throwError "Trait law changed its generated ownership or original dictionary prefix: {lawName}"
  let actualLaws := registered.filterMap (·.law)
  unless actualLaws.size == expectedLaws.size && actualLaws.all expectedLaws.contains do
    throwError "Compiled trait laws disagree with annotated Rust traits"
  let some funsModule := env.getModuleIdx? `Zerocopy.Funs
    | throwError "Extracted implementation dictionaries must be imported"
  let mut requiredImplementations : Array Name := #[]
  let mut requiredWitnesses : Array Name := #[]
  for row in implementations do
    let .ok dictionary := row.getObjValAs? String "dictionary"
      | throwError "Required trait implementation must name its exact dictionary"
    let .ok law := row.getObjValAs? String "law"
      | throwError "Required trait implementation must name its law class"
    let .ok proof := row.getObjValAs? String "proof"
      | throwError "Required trait implementation must name its proof"
    let dictionaryName := dictionary.toName
    let proofName := proof.toName
    if requiredImplementations.contains dictionaryName then
      throwError "Repeated required trait implementation {dictionaryName}"
    requiredImplementations := requiredImplementations.push dictionaryName
    unless expectedLaws.contains law.toName &&
        env.getModuleIdxFor? dictionaryName == some funsModule do
      throwError "Trait implementation has an unexpected law or compiled owner: {dictionaryName}"
    let some (.thmInfo proofInfo) := env.find? proofName
      | throwError "Missing ordinary trait implementation theorem {proofName}"
    unless (env.getModuleIdxFor? proofName).any proofModules.contains do
      throwError "Trait implementation theorem must belong to a configured proof module: {proofName}"
    let .ok typeCount := row.getObjValAs? Nat "generic_count"
      | throwError "Trait implementation must count its original type parameters"
    let .ok constCount := row.getObjValAs? Nat "const_count"
      | throwError "Trait implementation must count its original const parameters"
    let .ok dictionaryCount := row.getObjValAs? Nat "dictionary_count"
      | throwError "Trait implementation must count its original dictionaries"
    let .ok constParameters := row.getObjValAs? (Array Json) "const_parameters"
      | throwError "Trait implementation must retain its original usize const identities"
    unless constParameters.size == constCount do
      throwError "Trait implementation changed its original const inventory"
    AeneasSpecs.checkTraitImplementationNativeParameters dictionaryName
      typeCount constCount dictionaryCount constParameters
    let expected ← AeneasSpecs.traitImplementationObligation law.toName dictionaryName
    unless ← Meta.isDefEq proofInfo.type expected do
      throwError "Trait implementation theorem changed its exact dictionary or premises: {proofName}"
    -- Inspect the authored telescope separately from obligation generation.
    -- The deterministic witness is a normal kernel theorem owned by Required,
    -- whose value must directly reuse this exact configured authored theorem.
    AeneasSpecs.auditTraitImplementationProof law.toName dictionaryName proofName
    let witnessName := AeneasSpecs.traitImplementationWitnessName dictionaryName
    requiredWitnesses := requiredWitnesses.push witnessName
    let some (.thmInfo witness) := env.find? witnessName
      | throwError "Missing kernel-checked trait implementation witness {witnessName}"
    let some requiredModule := env.getModuleIdx? `Required
      | throwError "Missing required checks module"
    unless env.getModuleIdxFor? witnessName == some requiredModule do
      throwError "Trait implementation witness has the wrong compiled owner: {witnessName}"
    unless witness.value.isConstOf proofName do
      throwError "Trait implementation witness must directly use its authored theorem: {witnessName}"
    unless ← Meta.isDefEq witness.type expected do
      throwError "Trait implementation witness changed its native obligation: {witnessName}"
    AeneasSpecs.auditTraitImplementationProof law.toName dictionaryName witnessName
  -- Enumerate the compiled dictionaries independently of Aeneas's JSON names.
  -- Even a swapped name or omitted row in that metadata cannot leave an actual
  -- extracted implementation of an annotated trait without its checked law.
  let mut actualImplementations : Array Name := #[]
  for (declName, info) in env.constants.toList do
    if env.getModuleIdxFor? declName != some funsModule then continue
    let .defnInfo info := info | continue
    let annotated ← Meta.forallTelescope info.type fun _ result => do
      return ((← AeneasSpecs.traitDictionary? result).bind (·.law)).isSome
    if annotated then actualImplementations := actualImplementations.push declName
  unless actualImplementations.size == requiredImplementations.size &&
      actualImplementations.all requiredImplementations.contains do
    throwError "Compiled trait implementations disagree with required law coverage: actual {actualImplementations}; required {requiredImplementations}"
  let some requiredModule := env.getModuleIdx? `Required
    | throwError "Missing required checks module"
  let actualWitnesses := env.constants.toList.filterMap fun (witnessName, info) =>
    if env.getModuleIdxFor? witnessName == some requiredModule &&
        witnessName.getString!.endsWith "_trait_law_checked" then
      match info with
      | .thmInfo _ => some witnessName
      | _ => none
    else none
  unless actualWitnesses.length == requiredWitnesses.size &&
      actualWitnesses.all requiredWitnesses.contains do
    throwError "Compiled trait implementation witnesses disagree with required coverage"
  -- Compare registered providers too: a raw type can be present in extraction
  -- and the manifest while its full mathematical provider is absent or extra.
  let actualOwners := (← AeneasSpecs.modelOwnerNames).filter
    (fun owner => env.getModuleIdxFor? (owner ++ `aeneasModel) == some modelsModule)
  let missingOwners := expectedTypes.filter (!actualOwners.contains ·)
  let extraOwners := actualOwners.filter (!expectedTypes.contains ·)
  unless missingOwners.isEmpty && extraOwners.isEmpty do
    throwError "Compiled mathematical models disagree with bindings: missing {missingOwners}; unexpected {extraOwners}"
  let missing := expectedModels.filter (fun modelName => !actualModels.contains modelName)
  let extra := actualModels.filter (fun modelName => !expectedModels.contains modelName)
  unless missing.isEmpty && extra.isEmpty do
    throwError "Compiled inline specification models disagree with bindings: missing {missing}; unexpected {extra}"
  -- The backend's Option.ofResult erases every failure into a normal None,
  -- including undef. That is not a supported Rust recovery operation here.
  -- Follow downstream compiled dependencies, including helpers and opaque
  -- bodies, so hiding this adapter behind another local definition cannot
  -- admit it. Stop at the pinned backend: its checked integer primitives use
  -- this adapter internally to represent arithmetic overflow as Rust's None.
  -- Their implementation is already part of the trusted translation boundary.
  -- Identify that boundary by compiled module ownership, not a declaration's
  -- namespace, so a downstream helper cannot impersonate a backend primitive.
  -- This conservative check rejects even unreachable local dependencies; it
  -- does not certify arbitrary external models as faithful Rust semantics.
  let mut pendingModels := actualModels
  let mut visitedModels : NameHashSet := {}
  while !pendingModels.isEmpty do
    let current := pendingModels.back!
    pendingModels := pendingModels.pop
    if visitedModels.contains current then continue
    visitedModels := visitedModels.insert current
    if current == `Aeneas.Std.Option.ofResult then
      throwError "Extracted execution depends on unsupported failure erasure: {current}"
    if let some owner := env.getModuleIdxFor? current then
      let moduleName := env.allImportedModuleNames[owner.toNat]!
      if moduleName.getRoot == `Aeneas && !auditModules.contains owner then continue
    let some info := env.find? current
      | throwError "Missing execution dependency {current}"
    pendingModels := pendingModels ++ info.type.getUsedConstants ++
      ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
  -- Sort only for reproducible diagnostics and dependency output. Coverage was
  -- established from complete sets above, independent of declaration order.
  required := required.qsort (fun a b => a.toString < b.toString)
  let some checksModule := env.getModuleIdx? `Required
    | throwError "Required checks must be imported from their own module"
  for declName in required do
    let some (.thmInfo info) := env.find? declName
      | throwError "Missing required theorem {declName}"
    let specName := (`Zerocopy.Specs).str declName.getString!
    unless env.contains specName do
      throwError "Missing inline specification {specName}"
    -- Require the canonical theorem's type to name its exact spec. An arbitrary
    -- term or independently reproved proposition could bypass the inline claim.
    let actualSpec ← AeneasContracts.canonicalSpecName declName
    unless actualSpec == specName do
      throwError "{declName} must directly name its inline specification {specName}"
    unless ← Meta.isDefEq info.type (mkConst specName) do
      throwError "{declName} does not prove its inline specification {specName}"
    AeneasSpecs.checkSpecContract specName
    unless (env.getModuleIdxFor? declName).any proofModules.contains do
      throwError "{declName} must be declared in a configured proof module"
    let obligationName := (`Zerocopy.Obligations).str declName.getString!
    let adequacyName := obligationName.appendAfter "_adequate"
    let some (.thmInfo adequacy) := env.find? adequacyName
      | throwError "Missing arbitrary-outcome required theorem {adequacyName}"
    -- Reconstruct the arbitrary-outcome implication from compiled families.
    -- A concrete checked theorem alone would not expose weak posts, accidental
    -- divergence allowance, or a decoder/ghost that narrowed the required domain.
    let adequacyType ← AeneasContracts.contractAdequacyType specName obligationName
    unless ← Meta.isDefEq adequacy.type adequacyType do
      throwError "{adequacyName} does not prove its arbitrary-outcome required implication"
    unless env.getModuleIdxFor? adequacyName == some checksModule do
      throwError "{adequacyName} must be declared in the required checks module"
    -- The concrete witness is the separately named required proposition, and
    -- must be owned by the check module along with the adequacy theorem.
    let witnessName := obligationName.appendAfter "_checked"
    let some (.thmInfo witness) := env.find? witnessName
      | throwError "Missing independent required theorem {witnessName}"
    unless ← Meta.isDefEq witness.type (mkConst obligationName) do
      throwError "{witnessName} does not prove its independent required proposition"
    unless env.getModuleIdxFor? witnessName == some checksModule do
      throwError "{witnessName} must be declared in the required checks module"
  let mut graph : Array Json := #[]
  for declName in required do
    -- Follow helpers in every audited handwritten and model module, including
    -- private and generated declarations. Stop at registered callees, whose
    -- own edges follow. Canonical proof ownership remains restricted above.
    let mut pending := #[declName]
    let mut visited : NameHashSet := {}
    let mut actual : Array Name := #[]
    while !pending.isEmpty do
      let current := pending.back!
      pending := pending.pop
      if visited.contains current then continue
      visited := visited.insert current
      let some info := env.find? current
        | throwError "Missing proof declaration {current}"
      let references := info.type.getUsedConstants ++
        ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
      for used in references do
        if used == declName then continue
        if required.contains used then
          unless actual.contains used do actual := actual.push used
        else if (env.getModuleIdxFor? used).any auditModules.contains then
          pending := pending.push used
    actual := actual.qsort (fun a b => a.toString < b.toString)
    graph := graph.push (Json.mkObj [
      ("theorem", Json.str declName.toString),
      ("depends_on", Json.arr (actual.map (Json.str ∘ Name.toString)))])
  logInfo m!"Recorded proof dependencies of {required.size} theorems"
  -- Audit generated specs/models and handwritten helpers, not only canonical
  -- roots. A helper with an unapproved axiom must fail even if a current proof
  -- happens not to use it. privateToUserName keeps private namespace helpers in
  -- scope; module ownership catches auxiliaries with compiler-generated names.
  let prefixes := #[`Zerocopy, `core.num, `AeneasContracts, `AeneasSpecs,
    `ContractTests, `SpecsSyntaxTests, `SupportTests, `ContractAuditTests]
  let mut audited := 0
  for (declName, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf (privateToUserName declName)) ||
        (env.getModuleIdxFor? declName).any auditModules.contains ||
        env.getModuleIdxFor? declName == some checksModule then
      let used ← collectAxioms declName
      for ax in used do
        -- These are Lean's permitted logical axioms. The only additional
        -- allowances are the ABI data inputs and opaque carrier whose exact
        -- signatures were checked above. Neither supplies a proposition;
        -- sorryAx and user-defined proof axioms remain errors.
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax ||
            modelInputs.contains ax || opaqueCarriers.contains ax do
          throwError "{declName} depends on unapproved axiom {ax}"
      audited := audited + 1
  IO.FS.writeFile "proof-dependencies.json" (Json.arr graph).pretty
  logInfo m!"Checked axiom dependencies of {audited} declarations"
