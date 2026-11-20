import Miri.Input.Model

namespace Miri.Input
open Lean DecoderValues

private partial def collectFunctionAbisAux (node : JsonTraversalCache.Node) (path : String) (memo : DecodeMemo)
    (seen : Std.HashSet JsonTraversalCache.Key := {}) (visited : Std.HashSet JsonTraversalCache.IdentityKey := {})
    : Except String (Array FunctionAbi × Std.HashSet JsonTraversalCache.Key × Std.HashSet JsonTraversalCache.IdentityKey) := do
  let j := node.value
  let key := node.identity
  if statusOf? j == some "debug_payload" then return (#[], seen, visited)
  let isContainer := match j with | .arr _ | .obj _ => true | _ => false
  if isContainer && node.shouldMemo && visited.contains key then return (#[], seen, visited)
  let visited := if isContainer && node.shouldMemo then visited.insert key else visited
  match j with
  | .arr values =>
    let mut all := #[]
    let mut seen := seen
    let mut visited := visited
    let mut index := 0
    for value in values do
      let (found, nextSeen, nextVisited) ← collectFunctionAbisAux (node.child index value) s!"{path}[{index}]" memo seen visited
      all := all ++ found
      seen := nextSeen
      visited := nextVisited
      index := index + 1
    return (all, seen, visited)
  | .obj fields =>
    let mut all := #[]
    let mut seen := seen
    let mut visited := visited
    for ((fieldName, value), childIndex) in fields.toList.zipIdx do
      let child := node.child childIndex value
      if fieldName == "fn_abi" && value != .null then
        let query? ← match statusOf? value with
          | some "supported" => pure (some (← field value "value" (joinPath path fieldName)))
          | some _ => pure none
          | none => pure (some value)
        if let some queryValue := query? then
          let queryKey := (if statusOf? value == some "supported" then
              child.field "value" queryValue else child).key
          if !seen.contains queryKey then
            all := all.push (← parseFunctionAbi queryValue (joinPath (joinPath path fieldName) "value") memo)
            seen := seen.insert queryKey
      let looksLikeFunctionAbi :=
        hasField value "arguments" && hasField value "return" &&
        hasField value "calling_convention" && hasField value "can_unwind" &&
        hasField value "c_variadic" && hasField value "fixed_count"
      if looksLikeFunctionAbi && !seen.contains child.key then
        all := all.push (← parseFunctionAbi value (joinPath path fieldName) memo)
        seen := seen.insert child.key
      let (found, nextSeen, nextVisited) ← collectFunctionAbisAux child (joinPath path fieldName) memo seen visited
      all := all ++ found
      seen := nextSeen
      visited := nextVisited
    return (all, seen, visited)
  | _ => return (#[], seen, visited)

private def collectFunctionAbis (node : JsonTraversalCache.Node) (path : String) (memo : DecodeMemo := emptyDecodeMemo) : Except String (Array FunctionAbi) := do
  return (← collectFunctionAbisAux node path memo).1

private def validateDense (ids : Array Nat) (what : String) : Except String Unit := do
  let mut seen : Std.HashSet Nat := {}
  for id in ids do
    if seen.contains id then throw s!"{what}: duplicate IDs"
    seen := seen.insert id
  for id in ids do
    if id >= ids.size then throw s!"{what}: IDs must be dense from zero; found {id} with {ids.size} entries"

/-- The bounds encode ID membership only after all three source ID arrays pass
`validateDense`; each dense array then denotes exactly the natural range below
its size, independent of row order. -/
private partial def validateReferencesAux (node : JsonTraversalCache.Node) (path : String)
    (typeCount allocationCount instanceCount : Nat) (visited : Std.HashSet JsonTraversalCache.IdentityKey)
    : Except String (Std.HashSet JsonTraversalCache.IdentityKey) := do
  let j := node.value
  let memoKey := node.identity
  if statusOf? j == some "debug_payload" then return visited
  let isContainer := match j with | .arr _ | .obj _ => true | _ => false
  if isContainer && node.shouldMemo && visited.contains memoKey then return visited
  match j with
  | .arr values =>
    let mut index := 0
    let mut visited := visited
    for value in values do
      visited ← validateReferencesAux (node.child index value) s!"{path}[{index}]" typeCount allocationCount instanceCount visited
      index := index + 1
    return if node.shouldMemo then visited.insert memoKey else visited
  | .obj fields =>
    let entries := fields.toList
    match entries with
    | [("type_id", idJson)] =>
      let id ← idJson.getNat? |>.mapError fun e => s!"{path}.type_id: malformed type reference ({e})"
      if id >= typeCount then throw s!"{path}: dangling type reference {id}"
      return if node.shouldMemo then visited.insert memoKey else visited
    | [("allocation_id", idJson)] =>
      let id ← idJson.getNat? |>.mapError fun e => s!"{path}.allocation_id: malformed allocation reference ({e})"
      if id >= allocationCount then throw s!"{path}: dangling allocation reference {id}"
      return if node.shouldMemo then visited.insert memoKey else visited
    | _ => pure ()
    let mut visited := visited
    for ((key, value), childIndex) in entries.zipIdx do
      if key == "instance_id" then
        let id ← value.getNat? |>.mapError fun e => s!"{joinPath path key}: malformed instance ID ({e})"
        if id >= instanceCount then throw s!"{joinPath path key}: dangling instance reference {id}"
      visited ← validateReferencesAux (node.child childIndex value) (joinPath path key) typeCount allocationCount instanceCount visited
    return if node.shouldMemo then visited.insert memoKey else visited
  | _ => return visited

private def validateReferences (node : JsonTraversalCache.Node) (path : String)
    (typeCount allocationCount instanceCount : Nat) : Except String Unit := do
  let _ ← validateReferencesAux node path typeCount allocationCount instanceCount {}

private partial def validateMirIndices (j : Json) (path : String)
    (localCount : Nat) : Except String Unit := do
  if statusOf? j == some "debug_payload" then return
  match j with
  | .arr values =>
    let mut index := 0
    for value in values do
      validateMirIndices value s!"{path}[{index}]" localCount
      index := index + 1
  | .obj fields =>
    for (key, value) in fields.toList do
      if key == "local" then
        let id ← value.getNat? |>.mapError fun e => s!"{joinPath path key}: expected local index ({e})"
        if id >= localCount then throw s!"{joinPath path key}: local {id} is out of range (locals={localCount})"
      if key == "projection" then
        let projections ← value.getArr? |>.mapError fun e => s!"{joinPath path key}: expected projection array ({e})"
        for (projection, index) in projections.toList.zipIdx do
          let pPath := s!"{joinPath path key}[{index}]"
          let kind ← fieldString projection "kind" pPath
          if kind == "Index" then
            let id ← fieldNat projection "local" pPath
            if id >= localCount then throw s!"{pPath}.local: local {id} is out of range (locals={localCount})"
          if kind == "ConstantIndex" then
            let _ ← fieldNat projection "offset" pPath
            let _ ← fieldNat projection "min_length" pPath
            let _ ← fieldBool projection "from_end" pPath
          if kind == "Subslice" then
            let _ ← fieldNat projection "from" pPath
            let _ ← fieldNat projection "to" pPath
            let _ ← fieldBool projection "from_end" pPath
          if kind == "Field" then
            let _ ← fieldNat projection "index" pPath
            let _ ← field projection "field_type" pPath
          if kind == "Downcast" then
            let _ ← fieldNat projection "variant_index" pPath
          if kind == "OpaqueCast" then let _ ← field projection "cast_type" pPath
          if kind == "UnwrapUnsafeBinder" then let _ ← field projection "inner_type" pPath
          if isKnownProjection kind then let _ ← field projection "resulting_type" pPath
      validateMirIndices value (joinPath path key) localCount
  | _ => pure ()

private def checkBlockIndex (value : Json) (path : String) (blockCount : Nat) : Except String Unit := do
  let id ← value.getNat? |>.mapError fun e => s!"{path}: expected basic-block index ({e})"
  if id >= blockCount then throw s!"{path}: basic block {id} is out of range (blocks={blockCount})"

private def checkRequiredEdge (j : Json) (key path : String) (blockCount : Nat) : Except String Unit := do
  checkBlockIndex (← field j key path) (joinPath path key) blockCount

private def checkOptionalEdge (j : Json) (key path : String) (blockCount : Nat) : Except String Unit := do
  match optionalField j key with
  | none => throw s!"{path}: missing optional edge field `{key}`"
  | some .null => pure ()
  | some value => checkBlockIndex value (joinPath path key) blockCount

private def validateUnwind (j : Json) (path : String) (blockCount : Nat) : Except String Unit := do
  let kind ← fieldString j "kind" path
  if kind == "Cleanup" then checkRequiredEdge j "target" path blockCount

private def validateTerminatorEdges (j : Json) (path : String) (blockCount : Nat) : Except String Unit := do
  let variant ← fieldString j "variant" path
  match variant with
  | "Goto" => checkRequiredEdge j "target" path blockCount
  | "SwitchInt" =>
    checkRequiredEdge j "otherwise" path blockCount
    let targets ← arrayField j "targets" path
    for (target, index) in targets.toList.zipIdx do
      checkRequiredEdge target "target" s!"{joinPath path "targets"}[{index}]" blockCount
  | "Drop" =>
    checkRequiredEdge j "target" path blockCount
    checkOptionalEdge j "async_drop" path blockCount
    validateUnwind (← field j "unwind" path) (joinPath path "unwind") blockCount
  | "Call" =>
    checkOptionalEdge j "target" path blockCount
    validateUnwind (← field j "unwind" path) (joinPath path "unwind") blockCount
  | "Assert" =>
    checkRequiredEdge j "target" path blockCount
    validateUnwind (← field j "unwind" path) (joinPath path "unwind") blockCount
  | "Yield" =>
    checkRequiredEdge j "resume" path blockCount
    checkOptionalEdge j "drop" path blockCount
  | "FalseEdge" =>
    checkRequiredEdge j "real_target" path blockCount
    checkRequiredEdge j "imaginary_target" path blockCount
  | "FalseUnwind" =>
    checkRequiredEdge j "real_target" path blockCount
    validateUnwind (← field j "unwind" path) (joinPath path "unwind") blockCount
  | _ => pure ()

private def validateBody (j : Json) (path : String) : Except String Unit := do
  let locals ← arrayField j "locals" path
  let blocks ← arrayField j "basic_blocks" path
  if locals.isEmpty then throw s!"{joinPath path "locals"}: MIR body must declare the return local"
  if blocks.isEmpty then throw s!"{joinPath path "basic_blocks"}: MIR body must contain a start block"
  let mut index := 0
  for localDecl in locals do
    let id ← fieldNat localDecl "local" s!"{joinPath path "locals"}[{index}]"
    if id != index then throw s!"{joinPath path "locals"}[{index}]: local declarations must be densely ordered"
    index := index + 1
  index := 0
  for block in blocks do
    let blockPath := s!"{joinPath path "basic_blocks"}[{index}]"
    let id ← fieldNat block "block" blockPath
    if id != index then throw s!"{blockPath}: basic blocks must be densely ordered"
    let statements ← arrayField block "statements" blockPath
    for (statement, stmtIndex) in statements.toList.zipIdx do
      let kind ← field statement "kind" s!"{blockPath}.statements[{stmtIndex}]"
      validateMirIndices kind s!"{blockPath}.statements[{stmtIndex}].kind" locals.size
    let termWrapper ← field block "terminator" blockPath
    if termWrapper == .null then throw s!"{blockPath}: missing terminator"
    let term ← field termWrapper "kind" s!"{blockPath}.terminator"
    validateMirIndices term s!"{blockPath}.terminator.kind" locals.size
    validateTerminatorEdges term s!"{blockPath}.terminator.kind" blocks.size
    index := index + 1

private partial def validateAllBodiesAux (node : JsonTraversalCache.Node) (path : String) (visited : Std.HashSet JsonTraversalCache.IdentityKey)
    : Except String (Std.HashSet JsonTraversalCache.IdentityKey) := do
  let j := node.value
  let memoKey := node.identity
  if statusOf? j == some "debug_payload" then return visited
  let isContainer := match j with | .arr _ | .obj _ => true | _ => false
  if isContainer && node.shouldMemo && visited.contains memoKey then return visited
  match j with
  | .arr values =>
    let mut index := 0
    let mut visited := visited
    for value in values do
      visited ← validateAllBodiesAux (node.child index value) s!"{path}[{index}]" visited
      index := index + 1
    return if node.shouldMemo then visited.insert memoKey else visited
  | .obj fields =>
    let hasLocals := (j.getObjVal? "locals").isOk
    let hasBlocks := (j.getObjVal? "basic_blocks").isOk
    if hasLocals != hasBlocks then throw s!"{path}: body requires both locals and basic_blocks"
    if hasLocals && hasBlocks then validateBody j path
    let mut visited := visited
    for ((key, value), childIndex) in fields.toList.zipIdx do
      visited ← validateAllBodiesAux (node.child childIndex value) (joinPath path key) visited
    return if node.shouldMemo then visited.insert memoKey else visited
  | _ => return visited

private def validateAllBodies (node : JsonTraversalCache.Node) (path : String) : Except String Unit := do
  let _ ← validateAllBodiesAux node path {}

private def jsonToNatArray (nodes : Array α) (getId : α → Nat) : Array Nat := nodes.map getId

private def primitiveLayoutObligations (primitive : PrimitiveLayout) (path : String) : Array Obligation := Id.run do
  let mut issues := #[]
  match primitive.kind with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "kind"))
  | .integer =>
    if primitive.integerKind.isNone || primitive.signed.isNone then
      issues := issues.push ⟨path, "integer primitive layout is missing integer kind or signedness"⟩
    match primitive.integerKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath path "integer_kind"))
    | _ => pure ()
  | .float =>
    if primitive.floatKind.isNone then issues := issues.push ⟨path, "float primitive layout is missing float kind"⟩
    match primitive.floatKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath path "float_kind"))
    | _ => pure ()
  | .pointer =>
    if primitive.addressSpace.isNone then issues := issues.push ⟨path, "pointer primitive layout is missing address space"⟩
  return issues

private def scalarLayoutObligations (scalar : ScalarLayout) (path : String) : Array Obligation := Id.run do
  let mut issues := primitiveLayoutObligations scalar.primitive (joinPath path "primitive")
  match scalar.kind with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "kind"))
  | .initialized =>
    if scalar.validRange.isNone then issues := issues.push ⟨path, "initialized scalar layout is missing its valid range"⟩
  | .union => pure ()
  return issues

private def backendReprObligations (repr : BackendRepr) (path : String) : Array Obligation := Id.run do
  let mut issues := #[]
  match repr.kind with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "kind"))
  | _ => pure ()
  for (key, scalar) in [("scalar", repr.scalar), ("first", repr.first), ("second", repr.second), ("element", repr.element)] do
    match scalar with
    | some value => issues := issues ++ scalarLayoutObligations value (joinPath path key)
    | none => pure ()
  return issues

private def taggedNodeObligations (node : TaggedNode) (known : List String)
    (path description : String) : Array Obligation := Id.run do
  let mut issues := (statusObligation? node.status path).toArray
  if !known.contains node.tag then
    issues := issues.push ⟨joinPath path "kind", s!"unrecognized {description} tag `{node.tag}`"⟩
  return issues

private def canonicalAbiObligations (abi : CanonicalAbi) (path : String) : Array Obligation := Id.run do
  let mut issues := (statusObligation? abi.status path).toArray
  match abi.kind with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "kind"))
  | .arm =>
    match abi.armCall with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath path "arm_call"))
    | none => issues := issues.push ⟨joinPath path "arm_call", "ARM calling convention is missing its call kind"⟩
    | _ => pure ()
  | .interrupt =>
    match abi.interruptKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath path "interrupt_kind"))
    | none => issues := issues.push ⟨joinPath path "interrupt_kind", "interrupt calling convention is missing its interrupt kind"⟩
    | _ => pure ()
  | .x86 =>
    match abi.x86Call with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath path "x86_call"))
    | none => issues := issues.push ⟨joinPath path "x86_call", "x86 calling convention is missing its call kind"⟩
    | _ => pure ()
  | _ => pure ()
  return issues

private def externAbiObligations (abi : ExternAbi) (path : String) : Array Obligation := Id.run do
  let mut issues := taggedNodeObligations abi.kind
    ["c", "system", "rust", "rust_call", "rust_cold", "rust_invalid", "rust_preserve_none",
      "rust_tail", "llvm_intrinsic", "custom", "efi_api", "swift", "aapcs",
      "cmse_nonsecure_call", "cmse_nonsecure_entry", "gpu_kernel", "ptx_kernel",
      "avr_interrupt", "avr_non_blocking_interrupt", "msp430_interrupt",
      "riscv_interrupt_machine", "riscv_interrupt_supervisor", "x86_interrupt", "cdecl",
      "stdcall", "fastcall", "thiscall", "vectorcall", "sysv64", "win64"]
    path "extern ABI"
  let hasUnwindTag := ["c", "system", "aapcs", "cdecl", "stdcall", "fastcall", "thiscall", "vectorcall", "sysv64", "win64"].contains abi.kind.tag
  if hasUnwindTag && abi.unwind.isNone then
    issues := issues.push ⟨joinPath path "unwind", "this extern ABI requires an explicit unwind flag"⟩
  if !hasUnwindTag && abi.unwind.isSome then
    issues := issues.push ⟨joinPath path "unwind", "extern ABI has an unexpected unwind flag"⟩
  if abi.sourceSpelling.isNone then
    issues := issues.push ⟨joinPath path "source_spelling", "extern ABI is missing its original spelling"⟩
  return issues

private def abiAttributesObligations (attrs : AbiAttributes) (path : String) : Array Obligation := Id.run do
  let mut issues := taggedNodeObligations attrs.argExtension ["none", "zero_extend", "sign_extend"]
      (joinPath path "arg_extension") "argument extension"
  issues := issues ++ taggedNodeObligations attrs.captures ["none", "address", "read_only", "unrestricted"]
      (joinPath path "captures") "capture mode"
  return issues

private def abiRegisterObligations (reg : AbiRegister) (path : String) : Array Obligation := Id.run do
  let mut issues := #[]
  match reg.kind with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "kind"))
  | .vector =>
    match reg.hintElement with
    | none => issues := issues.push ⟨joinPath path "kind.hint_element", "vector ABI register is missing its element hint"⟩
    | some hint => issues := issues ++ taggedNodeObligations hint ["integer", "float", "pointer"] (joinPath path "kind.hint_element") "register element"
  | _ => pure ()
  return issues

private def abiPassModeObligations (mode : AbiPassMode) (path : String) : Array Obligation := Id.run do
  let mut issues := #[]
  match mode.kind with
  | .unknown tag => issues := issues.push ⟨joinPath path "kind", s!"unrecognized ABI pass mode `{tag}`"⟩
  | _ => pure ()
  for (attrs, index) in mode.attributes.toList.zipIdx do
    issues := issues ++ abiAttributesObligations attrs s!"{path}.attributes[{index}]"
  match mode.castTarget with
  | some target =>
    for (register, index) in target.prefixRegisters.toList.zipIdx do
      issues := issues ++ abiRegisterObligations register s!"{path}.target.prefix_registers[{index}]"
    issues := issues ++ abiRegisterObligations target.restRegister (joinPath path "target.rest_register")
    issues := issues ++ abiAttributesObligations target.attributes (joinPath path "target.attributes")
  | none => pure ()
  match mode.indirectMode with
  | some tag => issues := issues ++ taggedNodeObligations tag ["pointer", "on_stack", "amdgpu_kernel_argument"] (joinPath path "mode") "indirect mode"
  | none => pure ()
  return issues

private def allocationMemoryObligations (memory : AllocationMemory) (path : String) : Array Obligation := Id.run do
  let mut issues := #[]
  match memory.mutability with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "mutability"))
  | .mutable | .immutable => pure ()
  if memory.alignBytes == 0 then issues := issues.push ⟨joinPath path "align_bytes", "allocation alignment must be nonzero"⟩
  return issues

private def tagEncodingObligations (encoding : TagEncoding) (path : String) : Array Obligation := Id.run do
  let mut issues := (statusObligation? encoding.status path).toArray
  match encoding.kind with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "kind"))
  | .direct => pure ()
  | .niche =>
    if encoding.untaggedVariant.isNone || encoding.nicheVariants.isNone || encoding.nicheStart.isNone then
      issues := issues.push ⟨path, "niche tag encoding is missing its structured variant range or niche start"⟩
    match encoding.nicheVariants with
    | some (first, last) => if last < first then issues := issues.push ⟨joinPath path "niche_variants", "inclusive niche range has its end before its start"⟩
    | none => pure ()
  return issues

private def promotedBodyObligations (promoted : Array PromotedBody) (path : String) : Array Obligation := Id.run do
  let mut issues := #[]
  for entry in promoted do
    if entry.body.isNone then
      issues := issues.push ⟨s!"{path}[{entry.index}]", "promoted MIR body is absent; cannot import it as typed MIR"⟩
    if entry.status != .supported then
      if let some issue := statusObligation? entry.status s!"{path}[{entry.index}].status" then
        issues := issues.push issue
  return issues

private def virtualIdentityObligations (raw : Json) (types : Array TypeNode)
    (instances : Array InstanceNode) : Array Obligation := Id.run do
  let mut issues := #[]
  for (node, index) in instances.toList.zipIdx do
    if node.kind != .virtualDispatchTarget || node.status != .supported then continue
    let base := s!"$.instances[{index}]"
    let payload := node.payload
    if (payload.getObjValAs? String "body_status").toOption != some "not_applicable" then
      issues := issues.push ⟨base ++ ".body_status", "virtual dispatch identity must explicitly have no executable MIR body"⟩
    if node.body.isSome then
      issues := issues.push ⟨base ++ ".body", "virtual dispatch identity cannot carry a fabricated MIR body"⟩
    let kind := (payload.getObjVal? "instance_kind").toOption.getD .null
    if (kind.getObjValAs? String "kind").toOption != some "virtual" then
      issues := issues.push ⟨base ++ ".instance_kind.kind", "virtual dispatch target must retain rustc InstanceKind::Virtual"⟩
    if (kind.getObjVal? "def_id").toOption != (payload.getObjVal? "def_id").toOption then
      issues := issues.push ⟨base ++ ".instance_kind.def_id", "virtual InstanceKind DefId disagrees with catalog DefId"⟩
    if (kind.getObjVal? "dispatch_slot").toOption != (payload.getObjVal? "dispatch_slot").toOption then
      issues := issues.push ⟨base ++ ".instance_kind.dispatch_slot", "virtual InstanceKind slot disagrees with catalog slot"⟩
    let identity := (payload.getObjVal? "virtual_identity").toOption.getD .null
    if (identity.getObjValAs? String "status").toOption != some "supported" then
      issues := issues.push ⟨base ++ ".virtual_identity.status", "virtual method identity/signature query is unresolved"⟩
    let functionType := (identity.getObjVal? "function_type").toOption.getD .null
    let typeId := (functionType.getObjValAs? Nat "type_id").toOption
    match typeId with
    | none => issues := issues.push ⟨base ++ ".virtual_identity.function_type", "virtual method identity is missing its compiler function type"⟩
    | some id =>
      let typeMatches := types.filter (·.id == id)
      if typeMatches.size != 1 then
        issues := issues.push ⟨base ++ ".virtual_identity.function_type", "virtual method identity references a missing or ambiguous type"⟩
      else if let some ty := typeMatches[0]? then
        if ty.shapeKind != .functionPointer && ty.shapeKind != .functionDefinition then
          issues := issues.push ⟨base ++ ".virtual_identity.function_type", "virtual method identity type is not a compiler function value"⟩
    let abi := (identity.getObjVal? "fn_abi").toOption.getD .null
    if (abi.getObjValAs? String "status").toOption != some "supported" then
      issues := issues.push ⟨base ++ ".virtual_identity.fn_abi.status", "virtual method FnAbi query is unresolved"⟩
    let abiValue := (abi.getObjVal? "value").toOption
    let catalog := ((raw.getObjVal? "compiler_instance_abis").bind Json.getArr?).toOption.getD #[]
    let abiRows := catalog.filter fun row =>
      (row.getObjValAs? Nat "instance_id").toOption == some node.id &&
      (row.getObjVal? "instance_kind").toOption == (payload.getObjVal? "instance_kind").toOption &&
      (row.getObjVal? "generic_args").toOption == (payload.getObjVal? "generic_args").toOption
    if abiRows.size != 1 then
      issues := issues.push ⟨base ++ ".virtual_identity.fn_abi", "virtual identity must match one exact full-instance FnAbi query"⟩
    else if let some row := abiRows[0]? then
      let query := (row.getObjVal? "abi_query").toOption.getD .null
      if (query.getObjValAs? String "status").toOption != some "supported" then
        issues := issues.push ⟨base ++ ".virtual_identity.fn_abi", "matching full-instance FnAbi query is unresolved"⟩
      else if abiValue != (query.getObjVal? "value").toOption then
        issues := issues.push ⟨base ++ ".virtual_identity.fn_abi", "virtual identity FnAbi disagrees with the exact full-instance FnAbi query"⟩
  return issues

private def extraSemanticObligations (raw : Json) (types : Array TypeNode) (allocations : Array AllocationNode)
    (instances : Array InstanceNode) (functionAbis : Array FunctionAbi) (bodies : Array Body) : Array Obligation := Id.run do
  let mut issues := #[]
  issues := issues ++ virtualIdentityObligations raw types instances
  for node in types do
    match node.shapeKind with
    | .unknown tag => issues := issues.push (unknownTagObligation tag s!"types[{node.id}].shape.kind")
    | _ => pure ()
    let shapePath := s!"types[{node.id}].shape"
    if node.shapeStatus == .supported then
      match node.shapeKind, node.shapeMetadata.signedKind, node.shapeMetadata.unsignedKind,
          node.shapeMetadata.floatKind, node.shapeMetadata.adtKind with
      | .int, none, _, _, _ => issues := issues.push ⟨joinPath shapePath "signed_kind", "signed integer type shape is missing its exact integer type"⟩
      | .int, some (.known kind), _, _, _ =>
        if !kind.signed then
          issues := issues.push ⟨joinPath shapePath "signed_kind", "signed integer type shape carries an unsigned integer kind"⟩
      | .uint, _, none, _, _ => issues := issues.push ⟨joinPath shapePath "unsigned_kind", "unsigned integer type shape is missing its exact integer type"⟩
      | .uint, _, some (.known kind), _, _ =>
        if kind.signed then
          issues := issues.push ⟨joinPath shapePath "unsigned_kind", "unsigned integer type shape carries a signed integer kind"⟩
      | .float, _, _, none, _ => issues := issues.push ⟨joinPath shapePath "float_kind", "float type shape is missing its exact float type"⟩
      | .adt, _, _, _, none => issues := issues.push ⟨joinPath shapePath "adt_kind", "ADT type shape is missing its struct/union/enum kind"⟩
      | _, _, _, _, _ => pure ()
    match node.shapeMetadata.signedKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath shapePath "signed_kind"))
    | _ => pure ()
    match node.shapeMetadata.unsignedKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath shapePath "unsigned_kind"))
    | _ => pure ()
    match node.shapeMetadata.floatKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath shapePath "float_kind"))
    | _ => pure ()
    match node.shapeMetadata.adtKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath shapePath "adt_kind"))
    | _ => pure ()
    match node.layout.kind with
    | .unknown tag => issues := issues.push (unknownTagObligation tag s!"types[{node.id}].layout.kind")
    | .layoutQueryError => issues := issues.push ⟨s!"types[{node.id}].layout", "rustc could not provide a concrete type layout"⟩
    | .layout => pure ()
    match node.layout.variantsKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag s!"types[{node.id}].layout.variants.kind")
    | _ => pure ()
    match node.layout.backendReprKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag s!"types[{node.id}].layout.backend_repr.kind")
    | _ => pure ()
    match node.layout.fields with
    | some fields =>
      match fields.kind with
      | .unknown tag => issues := issues.push (unknownTagObligation tag s!"types[{node.id}].layout.fields.kind")
      | _ => pure ()
    | none => pure ()
    match node.layout.backendRepresentation with
    | some repr => issues := issues ++ backendReprObligations repr s!"types[{node.id}].layout.backend_repr"
    | none => pure ()
    match node.layout.variantsLayout with
    | some variants =>
      match variants.kind with
      | .unknown tag => issues := issues.push (unknownTagObligation tag s!"types[{node.id}].layout.variants.kind")
      | _ => pure ()
      match variants.tagEncoding with
      | some encoding => issues := issues ++ tagEncodingObligations encoding s!"types[{node.id}].layout.variants.tag_encoding"
      | none => if variants.kind == .multiple then issues := issues.push ⟨s!"types[{node.id}].layout.variants.tag_encoding", "multi-variant layout is missing tag encoding"⟩
      match variants.tag with
      | some scalar => issues := issues ++ scalarLayoutObligations scalar s!"types[{node.id}].layout.variants.tag"
      | none => pure ()
      for variant in variants.variants do
        issues := issues ++ backendReprObligations variant.backendRepr s!"types[{node.id}].layout.variants[{variant.variantIndex}].backend_repr"
    | none => pure ()
    match node.signature with
    | some signature =>
      issues := issues ++ taggedNodeObligations signature.safety ["safe", "unsafe"]
        s!"types[{node.id}].shape.signature.safety" "function safety"
      issues := issues ++ externAbiObligations signature.abi s!"types[{node.id}].shape.signature.abi"
    | none => pure ()
  for node in allocations do
    let allocPath := s!"allocations[{node.id}]"
    match node.kind, node.data with
    | .unknown, _ => issues := issues.push ⟨s!"{allocPath}.kind", "allocation kind is missing"⟩
    | .other tag, _ => issues := issues.push ⟨s!"{allocPath}.kind", s!"unrecognized allocation kind `{tag}`"⟩
    | .memory, some (.memory memory) =>
      issues := issues ++ allocationMemoryObligations memory allocPath
    | .function, some (.function function) =>
      if function.definitionPath.isEmpty then issues := issues.push ⟨s!"{allocPath}.instance_def_path", "function allocation is missing its definition path"⟩
    | .static, some (.static static) =>
      if static.definitionPath.isEmpty then issues := issues.push ⟨s!"{allocPath}.def_path", "static allocation is missing its definition path"⟩
      match static.initializer, static.globalInfo with
      | some initializer, _ =>
        issues := issues ++ allocationMemoryObligations initializer (joinPath allocPath "initializer")
      | none, some info =>
        if !info.foreignItem then issues := issues.push ⟨joinPath allocPath "initializer", "non-foreign static is missing its initializer image"⟩
      | none, none =>
        issues := issues.push ⟨joinPath allocPath "initializer", "static without an initializer lacks exact foreign-item compiler evidence"⟩
    | .vtable, some (.vtable vtable) =>
      if let some issue := statusObligation? vtable.layoutStatus s!"{allocPath}.layout_status" then issues := issues.push issue
      for (predicate, index) in vtable.predicates.toList.zipIdx do
        let pPath := s!"{allocPath}.predicates[{index}]"
        if let some issue := statusObligation? predicate.status (joinPath pPath "status") then issues := issues.push issue
        match predicate.kind with
        | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath pPath "kind"))
        | _ => pure ()
      for (entry, index) in vtable.entries.toList.zipIdx do
        let ePath := s!"{allocPath}.entries[{index}]"
        if let some issue := statusObligation? entry.status (joinPath ePath "status") then issues := issues.push issue
        match entry.kind with
        | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath ePath "kind"))
        | _ => pure ()
    | .typeId, some (.typeId _) => pure ()
    | _, none => if node.status == .supported then issues := issues.push ⟨allocPath, "supported allocation is missing its typed payload"⟩
    | _, some _ => issues := issues.push ⟨allocPath, "allocation kind and typed payload disagree"⟩
  for node in instances do
    match node.kind with
    | .other tag => issues := issues.push ⟨s!"instances[{node.id}].kind", s!"unrecognized instance kind `{tag}`"⟩
    | .instanceMirTemplate => issues := issues.push ⟨s!"instances[{node.id}].kind", "generic MIR template is not a substituted executable instance body"⟩
    | .instanceMir =>
      if node.body.isNone then
        issues := issues.push ⟨s!"instances[{node.id}].body", "instance MIR is missing its decoded body"⟩
      match node.bodyInstantiation with
      | none => issues := issues.push ⟨s!"instances[{node.id}].body_instantiation", "instance body is missing substitution/normalization evidence"⟩
      | some detail =>
        if let some issue := statusObligation? detail.status s!"instances[{node.id}].body_instantiation.status" then issues := issues.push issue
        if detail.tag != "substituted_and_normalized" then
          issues := issues.push ⟨s!"instances[{node.id}].body_instantiation.kind", s!"unsupported instance body transformation `{detail.tag}`"⟩
      if node.bodyTemplateIsPolymorphic.isNone then
        issues := issues.push ⟨s!"instances[{node.id}].body_template_is_polymorphic", "instance lacks polymorphism metadata for its body template"⟩
      if node.instanceArgsAreMonomorphic != some true then
        issues := issues.push ⟨s!"instances[{node.id}].instance_args_are_monomorphic", "instance arguments are not known to be monomorphic"⟩
    | .intrinsicWithoutMir => issues := issues.push ⟨s!"instances[{node.id}]", "intrinsic instance has no imported MIR body"⟩
    | .intrinsicDispatch =>
      let base := s!"instances[{node.id}]"
      if node.status != .supported then
        issues := issues.push ⟨joinPath base "status", "intrinsic dispatch identity is not supported by the source compiler facts"⟩
      if node.body.isSome then
        issues := issues.push ⟨joinPath base "body", "intrinsic dispatch identity cannot carry fabricated MIR"⟩
      let instanceKind := (node.payload.getObjVal? "instance_kind").toOption.getD .null
      let tag := (instanceKind.getObjValAs? String "kind").toOption
      if tag != some "intrinsic" && tag != some "llvm_intrinsic" then
        issues := issues.push ⟨joinPath base "instance_kind.kind", "intrinsic dispatch requires exact rustc Intrinsic or LlvmIntrinsic identity"⟩
      let topDefId := node.definitionId
      let nestedDefIdJson := (instanceKind.getObjVal? "def_id").toOption
      let nestedDefId := nestedDefIdJson.bind fun value =>
        match value.getObjValAs? Nat "crate", value.getObjValAs? Nat "index" with
        | .ok crate, .ok index => some ⟨crate, index⟩
        | _, _ => none
      if topDefId.isNone then
        issues := issues.push ⟨joinPath base "def_id", "intrinsic dispatch requires an exact top-level rustc DefId"⟩
      if nestedDefId.isNone then
        issues := issues.push ⟨joinPath base "instance_kind.def_id", "intrinsic dispatch requires an exact nested rustc DefId"⟩
      if topDefId.isSome && nestedDefId.isSome && topDefId != nestedDefId then
        issues := issues.push ⟨joinPath base "instance_kind.def_id", "intrinsic identity DefId disagrees with its instance record"⟩
    | .foreignItemNoMir =>
      let base := s!"instances[{node.id}]"
      if node.status != .supported then
        issues := issues.push ⟨joinPath base "status", "foreign item dispatch identity is not supported by source compiler facts"⟩
      if node.body.isSome then
        issues := issues.push ⟨joinPath base "body", "foreign declaration cannot carry fabricated MIR"⟩
      if (node.payload.getObjValAs? Bool "foreign_item").toOption != some true then
        issues := issues.push ⟨joinPath base "foreign_item", "no-MIR foreign dispatch requires exact rustc is_foreign_item=true evidence"⟩
      let symbol := (node.payload.getObjVal? "symbol_name").toOption.getD .null
      if (symbol.getObjValAs? String "status").toOption != some "supported" ||
          ((symbol.getObjValAs? String "value").toOption.getD "").isEmpty then
        issues := issues.push ⟨joinPath base "symbol_name", "no-MIR foreign dispatch requires an exact nonempty rustc symbol name"⟩
      let instanceKind := (node.payload.getObjVal? "instance_kind").toOption.getD .null
      if (instanceKind.getObjValAs? String "kind").toOption != some "item" then
        issues := issues.push ⟨joinPath base "instance_kind.kind", "foreign dispatch requires exact rustc Item identity"⟩
      let topDefId := node.definitionId
      let nestedDefIdJson := (instanceKind.getObjVal? "def_id").toOption
      let nestedDefId := nestedDefIdJson.bind fun value =>
        match value.getObjValAs? Nat "crate", value.getObjValAs? Nat "index" with
        | .ok crate, .ok index => some ⟨crate, index⟩
        | _, _ => none
      if topDefId.isNone then
        issues := issues.push ⟨joinPath base "def_id", "foreign dispatch requires an exact top-level rustc DefId"⟩
      if nestedDefId.isNone then
        issues := issues.push ⟨joinPath base "instance_kind.def_id", "foreign dispatch requires an exact nested rustc DefId"⟩
      if topDefId.isSome && nestedDefId.isSome && topDefId != nestedDefId then
        issues := issues.push ⟨joinPath base "instance_kind.def_id", "foreign identity DefId disagrees with its instance record"⟩
    | .virtualDispatch => issues := issues.push ⟨s!"instances[{node.id}]", "virtual dispatch operation lacks a complete abstract instance identity"⟩
    | .virtualDispatchTarget => pure ()
    | .instanceMirUnavailable => issues := issues.push ⟨s!"instances[{node.id}]", "rustc did not provide an instance MIR body"⟩
    | .symbolIdentityOnly =>
      if node.body.isSome then
        issues := issues.push ⟨s!"instances[{node.id}].body", "symbol identity catalog row must not provide an executable MIR body"⟩
  for (abi, abiIndex) in functionAbis.toList.zipIdx do
    issues := issues ++ canonicalAbiObligations abi.callingConvention s!"function_abis[{abiIndex}].calling_convention"
    for (arg, argIndex) in (abi.arguments.push abi.returnValue).toList.zipIdx do
      issues := issues ++ abiPassModeObligations arg.mode s!"function_abis[{abiIndex}].arguments[{argIndex}].mode"
  for (body, index) in bodies.toList.zipIdx do
    issues := issues ++ promotedBodyObligations body.promotedBodies s!"bodies[{index}].promoted_bodies"
  for node in instances do
    issues := issues ++ promotedBodyObligations node.promotedBodies s!"instances[{node.id}].promoted_bodies"
  return issues

private def selectedScopeObligations (scope : SelectedScope) (bodies : Array Body)
    (instances : Array InstanceNode) : Array Obligation := Id.run do
  let mut issues := #[]
  if scope.kind != "rooted_structural_closure" then
    issues := issues.push ⟨"$.selected_scope.kind", s!"unrecognized selected-scope kind `{scope.kind}`"⟩
  if scope.statusText != "complete" || scope.status != .supported then
    issues := issues.push ⟨"$.selected_scope.status", s!"selected scope is not complete (`{scope.statusText}`)"⟩
  if scope.semantics != "structural_export_closure_only" then
    issues := issues.push ⟨"$.selected_scope.semantics", s!"unrecognized scope guarantee `{scope.semantics}`"⟩
  if scope.roots.isEmpty then issues := issues.push ⟨"$.selected_scope.roots", "selected structural closure has no root"⟩
  for (root, index) in scope.roots.toList.zipIdx do
    let resolvedBody := bodies.any fun body =>
      body.definitionId == some root.definitionId && body.defPath == root.defPath
    let resolvedInstance := instances.any fun inst =>
      inst.definitionId == some root.definitionId && inst.defPath == some root.defPath
    if !resolvedBody && !resolvedInstance then
      issues := issues.push ⟨s!"$.selected_scope.roots[{index}]", "selected DefId and path do not resolve to an emitted body or instance"⟩
  if scope.unresolvedEvidence.isEmpty then
    for (message, index) in scope.unresolvedObligations.toList.zipIdx do
      issues := issues.push ⟨s!"$.selected_scope.unresolved_obligations[{index}]", message⟩
  else issues := issues ++ scope.unresolvedEvidence
  return issues

private def globalCompletenessPath (path : String) : Bool :=
  path == "$.completeness.status" || path.startsWith "$.completeness.unresolved_obligations["

/-- Query demand belongs to the interpreter entry that performs it. A selected
MIR structural closure does not perform startup exported-symbol traversal or
arbitrary foreign-shim catalog queries. Unknown families remain structural. -/
private inductive QueryDependencyRole where
  | structural | foreignShim | programStartup | callHelper | runtimeCast | intrinsicValue
  | nativeCallbackSignature | runtimeTypeQuery | namedPathStatic | runtimeVirtual
  | runtimeCallMetadata
  deriving BEq

/-- Only the checked status of an actual array-entry query is demand-local.
Unknown descendants and malformed paths remain structural obligations. -/
private def exactCatalogStatus (path catalog suffix : String) : Bool :=
  match path.splitOn "[" with
  | [head, tail] =>
    match tail.splitOn "]" with
    | [index, ending] => head == "$." ++ catalog && !index.isEmpty &&
        index.toList.all (fun c => '0' ≤ c && c ≤ '9') &&
        (index == "0" || !index.startsWith "0") && ending == suffix
    | _ => false
  | _ => false

private def exactVirtualResolutionStatus (path : String) : Bool :=
  match path.splitOn "[" with
  | [head, tail] =>
    match tail.splitOn "]" with
    | [index, suffix] => head == "$.compiler_runtime_queries.virtual" &&
        !index.isEmpty && index.toList.all (fun c => '0' ≤ c && c ≤ '9') &&
        (index == "0" || !index.startsWith "0") && suffix == ".resolved.status"
    | _ => false
  | _ => false

private def exactRuntimeInstanceFactStatus (path : String) : Bool :=
  match path.splitOn "[" with
  | [head, tail] =>
    match tail.splitOn "]" with
    | [index, suffix] => head == "$.compiler_runtime_queries.instances" &&
        !index.isEmpty && index.toList.all (fun c => '0' ≤ c && c ≤ '9') &&
        (index == "0" || !index.startsWith "0") &&
        [".symbol_name.status", ".item_name.status", ".intrinsic_metadata.status",
          ".codegen_symbol_name.status"].contains suffix
    | _ => false
  | _ => false

private def exactLibcTypeLayoutStatus (path : String) : Bool :=
  let prefixText := "$.compiler_libc_type_layouts.entries."
  let suffixText := ".status"
  if !path.startsWith prefixText || !path.endsWith suffixText then false else
    let name := ((path.drop prefixText.length).dropEnd suffixText.length).toString
    let known := #[
      "_umtx_time", "addrinfo", "clockid_t", "dirent", "dirent64", "epoll_event",
      "iovec", "linger", "mach_timebase_info", "mode_t", "nfds_t", "off_t",
      "os_unfair_lock_s", "passwd", "pollfd", "pthread_attr_t", "pthread_cond_t",
      "pthread_condattr_t", "pthread_key_t", "pthread_mutex_t", "pthread_mutexattr_t",
      "pthread_rwlock_t", "pthread_t", "sa_family_t", "sem_t", "size_t", "sockaddr",
      "sockaddr_in", "sockaddr_in6", "sockaddr_storage", "socklen_t", "stack_t", "statx",
      "time_t", "timespec", "timeval", "timezone", "tm", "utsname", "wchar_t"]
    known.contains name && path == prefixText ++ name ++ suffixText

/-- These are the finite source-path type queries emitted by
`shim_abi::named_types`. Only their status leaves are demand-local; the
catalog payload and any unrecognized key remain structural evidence. -/
private def exactCompilerNamedTypeStatus (path : String) : Bool :=
  let prefixText := "$.compiler_named_types."
  let suffixText := ".status"
  if !path.startsWith prefixText || !path.endsWith suffixText then false else
    let key := ((path.drop prefixText.length).dropEnd suffixText.length).toString
    let known := #[
      "c_ulong", "off_t", "off64_t", "pid_t", "uid_t", "nfds_t",
      "wchar_t", "pthread_t", "pthread_key_t",
      "libc_c_void", "libc_c_void_pointer", "libc_c_char", "libc_c_char_pointer",
      "libc_sockaddr", "libc_sockaddr_pointer", "libc_timespec", "libc_timespec_pointer",
      "libc_socklen_t", "libc_socklen_t_pointer", "libc_iovec", "libc_iovec_pointer",
      "u32_pointer", "i32_pointer"]
    known.contains key && path == prefixText ++ key ++ suffixText

private def exactDropGlueStatus (path : String) : Bool :=
  let prefixText := "$.compiler_runtime_queries.types["
  if !path.startsWith prefixText then false else
    let rest := (path.drop prefixText.length).toString
    match rest.splitOn "]" with
    | [index, suffix] => !index.isEmpty && index.toList.all (fun c => '0' ≤ c && c ≤ '9') &&
        (index == "0" || !index.startsWith "0") && suffix == ".drop_glue.status"
    | _ => false

private def exactInstanceCatalogPath (path : String) : Bool := Id.run do
  let path := if path.startsWith "$." then (path.drop 2).toString else path
  if !path.startsWith "instances[" then return false
  let rest := (path.drop 10).toString
  let pieces := rest.splitOn "]"
  let [index, suffix] := pieces | return false
  if index.isEmpty || !index.toList.all (fun c => '0' ≤ c && c ≤ '9') ||
      (index != "0" && index.startsWith "0") then return false
  return suffix == "" || suffix == ".status"

/-- Type rows are a compilation-wide catalog, while a rooted export can use
only a small part of that catalog. These exact leaves are compiler queries
whose status is checked by the corresponding runtime adapter when requested.
The whitelist deliberately excludes shape data and unknown descendants.
Required layout status is elevated independently below; compiler facts remain
demand-local and are checked when their exact providers are requested.
-/
private def exactTypeQueryStatus (path : String) : Bool := Id.run do
  if !path.startsWith "$.types[" then return false
  let rest := (path.drop 8).toString
  let parts := rest.splitOn "]"
  let [index, suffix] := parts | return false
  if index.isEmpty || !index.toList.all (fun c => '0' ≤ c && c ≤ '9') ||
      (index != "0" && index.startsWith "0") then return false
  if suffix == ".layout.status" then return true
  let exactQueries := #[
    ".compiler_facts.type_id_hash.status",
    ".compiler_facts.discriminants.status",
    ".compiler_facts.projection_queries.status",
    ".compiler_facts.simd_size_and_type.status",
    ".compiler_facts.boolean_queries.is_unsafe_cell.status",
    ".compiler_facts.boolean_queries.has_erasable_regions.status",
    ".compiler_facts.boolean_queries.is_c_void.status",
    ".compiler_facts.boolean_queries.is_simd.status",
    ".compiler_facts.boolean_queries.is_box.status",
    ".compiler_facts.boolean_queries.is_global_box.status",
    ".compiler_facts.boolean_queries.is_dynamic.status",
    ".compiler_facts.boolean_queries.is_too_generic.status",
    ".compiler_facts.boolean_queries.is_monomorphic.status",
    ".compiler_facts.boolean_queries.is_monomorphic_enough.status",
    ".compiler_facts.boolean_queries.is_like_maybe_dangling.status",
    ".compiler_facts.boolean_queries.is_freeze.status",
    ".compiler_facts.boolean_queries.is_unpin.status",
    ".compiler_facts.boolean_queries.is_unsafe_unpin.status",
    ".compiler_facts.boolean_queries.needs_drop.status",
    ".compiler_facts.boolean_queries.opsem_inhabited.status",
    ".compiler_facts.boolean_queries.is_sized.status",
    ".compiler_facts.type_queries.discriminant_type.status",
    ".compiler_facts.type_queries.normalized.status",
    ".compiler_facts.type_queries.builtin_deref_explicit.status",
    ".compiler_facts.type_queries.builtin_deref_implicit.status",
    ".compiler_facts.type_queries.boxed_type.status",
    ".compiler_facts.type_queries.unsafe_binder_erased.status",
    ".compiler_facts.type_queries.metadata_tail.status",
    ".compiler_facts.type_queries.pointer_metadata_type.status"]
  return suffix == ".shape.constructor_identity.status" || exactQueries.contains suffix

/-- Compute the type rows structurally demanded by the selected source graph.
This is independent of `selected_scope.unresolved_obligations`, so editing a
root type's layout status without editing the producer's diagnostic list cannot
make that required layout disappear. References in compiler_facts are excluded:
they are separate compiler queries and are checked by their exact providers.
-/
private partial def collectGraphReferencesInto (j : Json)
    (result : Array (String × Nat)) : Array (String × Nat) := Id.run do
  match j with
  | .obj fields =>
    if (j.getObjValAs? String "status").toOption == some "debug_payload" then return result
    let mut result := result
    for (key, value) in fields.toList do
      if key == "normalization_template" || key == "compiler_facts" || key == "constructor_identity" then
        continue
      if key == "type_id" || key == "instance_id" || key == "allocation_id" then
        if let .ok id := value.getNat? then result := result.push (key,id)
      result := collectGraphReferencesInto value result
    return result
  | .arr values =>
    let mut result := result
    for value in values do result := collectGraphReferencesInto value result
    return result
  | _ => return result

private def collectGraphReferences (j : Json) : Array (String × Nat) :=
  collectGraphReferencesInto j #[]

private def rawArray (j : Json) (key : String) : Array Json :=
  ((j.getObjVal? key).bind Json.getArr?).toOption.getD #[]

private partial def collectThreadLocalRefsInto (j : Json) (path : String)
    (found : Array (String × Json)) : Array (String × Json) := Id.run do
  match j with
  | .obj fields =>
    if (j.getObjValAs? String "status").toOption == some "debug_payload" then return found
    let mut found := if (j.getObjValAs? String "kind").toOption == some "ThreadLocalRef" then found.push ⟨path,j⟩ else found
    for (key, value) in fields.toList do
      found := collectThreadLocalRefsInto value (joinPath path key) found
    return found
  | .arr values =>
    let mut found := found
    let mut index := 0
    for value in values do
      found := collectThreadLocalRefsInto value s!"{path}[{index}]" found
      index := index + 1
    return found
  | _ => return found

private def collectThreadLocalRefs (j : Json) (path : String) : Array (String × Json) :=
  collectThreadLocalRefsInto j path #[]

private structure RequiredStructuralDependencies where
  typeIds : Array Nat := #[]
  instanceIds : Array Nat := #[]
  allocationIds : Array Nat := #[]
  threadLocalRefs : Array (String × Json) := #[]

private def requiredStructuralDependencies (j : Json) (includeAllBodies : Bool := false) : RequiredStructuralDependencies := Id.run do
  let roots := match optionalField j "selected_scope" with
    | some scope => rawArray scope "roots"
    | none => #[]
  if roots.isEmpty && !includeAllBodies then return {}
  let bodyRows := rawArray j "bodies"
  let instanceRows := rawArray j "instances"
  let allocationRows := rawArray j "allocations"
  let typeRows := rawArray j "types"
  -- Hash only the exact source definition path string. Candidate rows are
  -- checked with Json equality below, so arbitrary malformed Json values do
  -- not rely on a Json hash/equality law.
  let mut bodiesByDefinitionPath : Std.HashMap (Option String) (Array (Json × Nat)) := {}
  let mut indexedBodyPosition := 0
  for body in bodyRows do
    let key := ((body.getObjVal? "def_path").toOption.bind fun value => (value.getStr?).toOption)
    bodiesByDefinitionPath := bodiesByDefinitionPath.insert key
      ((bodiesByDefinitionPath[key]?.getD #[]).push (body, indexedBodyPosition))
    indexedBodyPosition := indexedBodyPosition + 1
  let mut instancesByDefinitionPath : Std.HashMap (Option String) (Array (Json × Nat)) := {}
  let mut instancesById : Std.HashMap Nat Json := {}
  for inst in instanceRows do
    let key := ((inst.getObjVal? "def_path").toOption.bind fun value => (value.getStr?).toOption)
    if let .ok id := (inst.getObjVal? "instance_id").bind Json.getNat? then
      instancesByDefinitionPath := instancesByDefinitionPath.insert key
        ((instancesByDefinitionPath[key]?.getD #[]).push (inst, id))
      if !(instancesById[id]?.isSome) then instancesById := instancesById.insert id inst
  let mut typesById : Std.HashMap Nat Json := {}
  for row in typeRows do
    if let .ok id := (row.getObjVal? "type_id").bind Json.getNat? then
      if !(typesById[id]?.isSome) then typesById := typesById.insert id row
  let mut allocationsById : Std.HashMap Nat Json := {}
  for row in allocationRows do
    if let .ok id := (row.getObjVal? "allocation_id").bind Json.getNat? then
      if !(allocationsById[id]?.isSome) then allocationsById := allocationsById.insert id row
  let mut requiredTls := #[]
  let mut pendingInstances := #[]
  let mut pendingAllocations := #[]
  let mut pendingTypes := #[]
  let (selectedBodies, selectedInstances) := if includeAllBodies && (optionalField j "selected_scope").isNone then
      (bodyRows.toList.zipIdx.toArray, #[])
    else Id.run do
      let mut selected := #[]
      let mut rootInstances := #[]
      for root in roots do
        let rootPath := (root.getObjVal? "def_path").toOption
        let rootDef := (root.getObjVal? "def_id").toOption
        let rootPathText := rootPath.bind fun value => (value.getStr?).toOption
        let rootBodyRows := (bodiesByDefinitionPath[rootPathText]?.getD #[]).filter fun (body, _) =>
          (body.getObjVal? "def_path").toOption == rootPath &&
            (body.getObjVal? "def_id").toOption == rootDef
        -- The canonical root instance is an independent structural dependency,
        -- even when its MIR body is emitted and does not refer to itself.
        for (inst, id) in instancesByDefinitionPath[rootPathText]?.getD #[] do
          if (inst.getObjVal? "def_path").toOption == rootPath &&
              (inst.getObjVal? "def_id").toOption == rootDef then
            rootInstances := rootInstances.push id
        selected := selected ++ rootBodyRows
      (selected, rootInstances)
  pendingInstances := pendingInstances ++ selectedInstances
  for (body,bodyIndex) in selectedBodies do
      for reference in collectThreadLocalRefs body s!"$.bodies[{bodyIndex}]" do
        requiredTls := requiredTls.push reference
      for (kind,id) in collectGraphReferences body do
        if kind == "type_id" then pendingTypes := pendingTypes.push id
        else if kind == "instance_id" then pendingInstances := pendingInstances.push id
        else if kind == "allocation_id" then pendingAllocations := pendingAllocations.push id
  let mut visitedTypes := #[]
  let mut visitedTypeIds : Std.HashMap Nat Unit := {}
  let mut visitedInstances := #[]
  let mut visitedInstanceIds : Std.HashMap Nat Unit := {}
  let mut visitedAllocations := #[]
  let mut visitedAllocationIds : Std.HashMap Nat Unit := {}
  while !pendingTypes.isEmpty || !pendingInstances.isEmpty || !pendingAllocations.isEmpty do
    let typeRefs := pendingTypes
    pendingTypes := #[]
    for id in typeRefs do
      if visitedTypeIds[id]?.isSome then continue
      visitedTypes := visitedTypes.push id
      visitedTypeIds := visitedTypeIds.insert id ()
      if let some row := typesById[id]? then
        -- Only the compiler's source type shape participates here. Layout
        -- evidence itself is demanded separately; compiler_facts is a query catalog.
        if let .ok shape := row.getObjVal? "shape" then
          for (kind, child) in collectGraphReferences shape do
            if kind == "type_id" then pendingTypes := pendingTypes.push child
            else if kind == "instance_id" then pendingInstances := pendingInstances.push child
            else if kind == "allocation_id" then pendingAllocations := pendingAllocations.push child
    let instanceRefs := pendingInstances
    pendingInstances := #[]
    for id in instanceRefs do
      if visitedInstanceIds[id]?.isSome then continue
      visitedInstances := visitedInstances.push id
      visitedInstanceIds := visitedInstanceIds.insert id ()
      if let some row := instancesById[id]? then
        for reference in collectThreadLocalRefs row s!"$.instances[{id}]" do
          requiredTls := requiredTls.push reference
        for (key,child) in collectGraphReferences row do
          if key == "type_id" then pendingTypes := pendingTypes.push child
          if key == "instance_id" then pendingInstances := pendingInstances.push child
          if key == "allocation_id" then pendingAllocations := pendingAllocations.push child
    let allocationRefs := pendingAllocations
    pendingAllocations := #[]
    for id in allocationRefs do
      if visitedAllocationIds[id]?.isSome then continue
      visitedAllocations := visitedAllocations.push id
      visitedAllocationIds := visitedAllocationIds.insert id ()
      if let some row := allocationsById[id]? then
        for (key,child) in collectGraphReferences row do
          if key == "type_id" then pendingTypes := pendingTypes.push child
          if key == "instance_id" then pendingInstances := pendingInstances.push child
          if key == "allocation_id" then pendingAllocations := pendingAllocations.push child
  return ⟨visitedTypes, visitedInstances, visitedAllocations, requiredTls⟩

/-- The prepared allocator-world parser validates every field in its raw
subtree. Its opaque graph rows remain visible in the decoded tree, but only
rows reached from executable bodies are structural readiness blockers. -/
private def preparedWorldReadinessObligations (obligations : Array Obligation)
    (world : Option CompilerAllocIdWorld) (allocations : Array AllocationNode)
    (requiredAllocationIds : Array Nat) : Array Obligation := Id.run do
  let some world := world | return obligations
  let mut requiredIds : Std.HashMap Nat Unit := {}
  for allocationId in requiredAllocationIds do
    requiredIds := requiredIds.insert allocationId ()
  let mut undemandedOpaqueIds : Std.HashMap Nat Unit := {}
  for row in world.rawPool do
    if row.status == .opaque then
      if let some allocationId := row.opaqueAllocationId then
        if !requiredIds.contains allocationId then
          undemandedOpaqueIds := undemandedOpaqueIds.insert allocationId ()
  let mut undemandedOpaqueIndexes : Std.HashMap Nat Unit := {}
  for (node, index) in allocations.toList.zipIdx do
    if undemandedOpaqueIds.contains node.id then
      undemandedOpaqueIndexes := undemandedOpaqueIndexes.insert index ()
  obligations.filter fun issue => Id.run do
    if issue.path.startsWith "$.compiler_alloc_id_world." then return false
    let arrayPrefix := "$.allocations["
    if issue.path.startsWith arrayPrefix then
      let rest := (issue.path.drop arrayPrefix.length).toString
      let indexText := (rest.takeWhile (· != ']')).toString
      if rest.startsWith (indexText ++ "]") then
        if let .ok index := decimalNat indexText issue.path then
          if undemandedOpaqueIndexes.contains index then return false
    let semanticPrefix := "allocations["
    if issue.path.startsWith semanticPrefix then
      let rest := (issue.path.drop semanticPrefix.length).toString
      let allocationText := (rest.takeWhile (· != ']')).toString
      if rest.startsWith (allocationText ++ "]") then
        if let .ok allocationId := decimalNat allocationText issue.path then
          if undemandedOpaqueIds.contains allocationId then return false
    return true

/-- Symbol-only entries close compiler identity references but carry no MIR.
Their absence of a body is harmless while they are unused catalog rows, but
any row reached from a selected root or executable graph is an unresolved
structural dependency. -/
private def requiredIdentityOnlyInstanceObligations (instances : Array InstanceNode)
    (requiredIds : Array Nat) : Array Obligation := Id.run do
  let mut issues := #[]
  for (node, index) in instances.toList.zipIdx do
    if requiredIds.contains node.id && node.kind == .symbolIdentityOnly then
      issues := issues.push ⟨s!"$.instances[{index}].kind",
        "selected execution depends on a symbol identity that has no imported MIR body"⟩
  return issues

private def threadLocalShapeObligations (references : Array (String × Json)) : Array Obligation := Id.run do
  let mut issues := #[]
  for (path, value) in references do
    unless (value.getObjValAs? String "status").toOption == some "supported" do continue
    let definition := (value.getObjVal? "def_id").toOption
    match definition with
    | none => issues := issues.push ⟨joinPath path "def_id", "supported ThreadLocalRef is missing its exact compiler DefId"⟩
    | some defId =>
      for key in ["crate", "index"] do
        if ((defId.getObjVal? key).bind Json.getNat?).toOption.isNone then
          issues := issues.push ⟨joinPath (joinPath path "def_id") key, "ThreadLocalRef DefId component must be an unsigned integer"⟩
    let info := (value.getObjVal? "global_info").toOption
    let mut foreign := false
    match info with
    | none => issues := issues.push ⟨joinPath path "global_info", "supported ThreadLocalRef is missing static compiler query evidence"⟩
    | some info =>
      if (info.getObjValAs? String "status").toOption != some "supported" then
        issues := issues.push ⟨joinPath (joinPath path "global_info") "status", "ThreadLocalRef static compiler query is unresolved"⟩
      if (info.getObjValAs? Bool "is_static").toOption != some true then
        issues := issues.push ⟨joinPath (joinPath path "global_info") "is_static", "ThreadLocalRef DefId is not confirmed as a static"⟩
      if (info.getObjValAs? Bool "thread_local").toOption != some true then
        issues := issues.push ⟨joinPath (joinPath path "global_info") "thread_local", "ThreadLocalRef DefId is not confirmed as thread-local"⟩
      foreign := (info.getObjValAs? Bool "is_foreign_item").toOption.getD false
      if (info.getObjValAs? Bool "is_foreign_item").toOption.isNone then
        issues := issues.push ⟨joinPath (joinPath path "global_info") "is_foreign_item", "ThreadLocalRef static query lacks its foreign-item predicate"⟩
    let initializer := (value.getObjVal? "initializer").toOption
    match initializer with
    | none => issues := issues.push ⟨joinPath path "initializer", "supported ThreadLocalRef is missing exact initializer query evidence"⟩
    | some initializer =>
      let initializerPath := joinPath path "initializer"
      if (initializer.getObjValAs? String "status").toOption == some "supported" then
        let allocation := (initializer.getObjVal? "allocation").toOption
        match allocation with
        | none => issues := issues.push ⟨joinPath initializerPath "allocation", "supported TLS initializer is missing its allocation image"⟩
        | some allocation =>
          let allocationPath := joinPath initializerPath "allocation"
          match parseAllocationMemory allocation allocationPath with
          | .error reason => issues := issues.push ⟨allocationPath, reason⟩
          | .ok memory =>
            if let some info := info then
              match (info.getObjVal? "size_bytes").bind Json.getNat? with
              | .ok size => if size != memory.sizeBytes then
                  issues := issues.push ⟨joinPath allocationPath "size_bytes", "TLS initializer size disagrees with static compiler query"⟩
              | .error _ => issues := issues.push ⟨joinPath (joinPath path "global_info") "size_bytes", "TLS static query is missing its allocation size"⟩
              match (info.getObjVal? "align_bytes").bind Json.getNat? with
              | .ok align => if align != memory.alignBytes then
                  issues := issues.push ⟨joinPath allocationPath "align_bytes", "TLS initializer alignment disagrees with static compiler query"⟩
              | .error _ => issues := issues.push ⟨joinPath (joinPath path "global_info") "align_bytes", "TLS static query is missing its allocation alignment"⟩
      else if foreign && (initializer.getObjValAs? String "status").toOption != some "unsupported" then
        issues := issues.push ⟨joinPath initializerPath "status", "foreign TLS initializer must remain an explicit unsupported query"⟩
  return issues

private def queryDependencyRole (path : String) : QueryDependencyRole :=
  if exactTypeQueryStatus path || exactDropGlueStatus path || exactInstanceCatalogPath path then .runtimeTypeQuery
  else if exactLibcTypeLayoutStatus path then .runtimeTypeQuery
  else if exactCompilerNamedTypeStatus path then .runtimeTypeQuery
  else if exactCatalogStatus path "compiler_named_constants" ".query.status" ||
      exactCatalogStatus path "compiler_named_constants" ".query.evaluation.status" ||
      exactCatalogStatus path "compiler_named_shim_abis" ".recipe.query.status" ||
      exactCatalogStatus path "compiler_named_shim_abis" ".recipe.query.abi_query.status" ||
      path == "$.compiler_runtime_queries.foreign_symbols.extern_statics.status" ||
      path == "$.compiler_runtime_queries.foreign_symbols.exported_candidates.status" then
    .foreignShim
  else if exactCatalogStatus path "compiler_named_statics" ".query.status" then .namedPathStatic
  else if exactCatalogStatus path "compiler_function_facts.helper_signatures" ".abi_query.status" then .callHelper
  -- Function type normalization and FnPtr ABI queries are catalogued for all
  -- exported types, then demanded only by the exact MIR call operation. The
  -- provider retains each failed query and reports it from the call hook.
  else if exactCatalogStatus path "compiler_function_facts.types" ".signature_query.status" ||
      exactCatalogStatus path "compiler_function_facts.pointer_abis" ".abi_query.status" then
    .runtimeCallMetadata
  -- Extern-static declaration and selected-export queries are materialized
  -- from the allocation graph, but their errors belong to exact symbol or
  -- DefId lookup at runtime, not to unrelated MIR paths. `compiler_fact`
  -- wraps the extern-static table in a `value` field; keep that envelope in
  -- each exact indexed path.
  else if exactCatalogStatus path "compiler_runtime_queries.foreign_symbols.extern_statics.value.declarations" ".status" ||
      exactCatalogStatus path "compiler_runtime_queries.foreign_symbols.extern_statics.value.selected_exported" ".status" ||
      exactCatalogStatus path "compiler_runtime_queries.foreign_symbols.extern_statics.value.selected_exported" ".declaration.status" ||
      exactCatalogStatus path "compiler_runtime_queries.foreign_symbols.extern_statics.value.selected_exported" ".allocation.status" then
    .foreignShim
  else if exactCatalogStatus path "compiler_cast_queries" ".status" then .runtimeCast
  -- These exact compiler call-fact queries are checked by their source-owned
  -- providers when an operation requests them; an unavailable optional row
  -- does not make an unrelated selected MIR body malformed.
  else if exactRuntimeInstanceFactStatus path then .runtimeCallMetadata
  -- Candidate virtual resolutions are a cross-product over compiler vtable
  -- pairs. A failed nonselected row is retained as source evidence; the exact
  -- receiver/type/args lookup rejects it if execution actually demands it.
  else if exactVirtualResolutionStatus path then .runtimeVirtual
  else if exactCatalogStatus path "compiler_type_name_constants" ".status" ||
      exactCatalogStatus path "compiler_caller_location_constants" ".status" then .intrinsicValue
  -- alloc_addresses/mod.rs:167–174 demands this only when constructing a
  -- native compiler-function closure; its provider checks signature_query.status.
  else if exactCatalogStatus path "compiler_native_signature_queries" ".signature_query.status" then
    .nativeCallbackSignature
  else if path == "$.compiler_main_queries.link_sections.status" then .programStartup
  else .structural

private def obligationQueryRole (path : String) : QueryDependencyRole :=
  let canonical := if path.startsWith "$." then path else "$." ++ path
  let direct := queryDependencyRole canonical
  if direct != .structural then direct
  else queryDependencyRole (canonical ++ ".status")

private def pathCanReach (wanted path : String) : Bool :=
  wanted == path || wanted.startsWith (path ++ ".") || wanted.startsWith (path ++ "[")

private def jsonAtPathSegment (j : Json) (segment : String) : Option Json := Id.run do
  match segment.splitOn "[" with
  | [key] => return (j.getObjVal? key).toOption
  | [key, suffix] =>
    let pieces := suffix.splitOn "]"
    let [indexText, ""] := pieces | return none
    let .ok index := decimalNat indexText segment | return none
    let some arrayJson := (j.getObjVal? key).toOption | return none
    let some values := arrayJson.getArr?.toOption | return none
    return values[index]?
  | _ => return none

def jsonAtPath (j : Json) (path : String) : Option Json := Id.run do
  unless path.startsWith "$." do return none
  let segments := (path.drop 2).toString.splitOn "."
  let mut current := some j
  for segment in segments do
    current := current.bind (fun value => jsonAtPathSegment value segment)
  return current

private def jsonTypeId? (j : Json) : Option Nat :=
  (j.getObjVal? "type_id").toOption.bind (fun value => value.getNat?.toOption)

private def dynamicPredicateArray? (j : Json) (typeId : Nat) : Option (Array Json) := Id.run do
  let some types := (((j.getObjVal? "types").bind Json.getArr?).toOption) | return none
  let matching := types.filter fun ty =>
    ((ty.getObjValAs? Nat "type_id").toOption == some typeId)
  unless matching.size == 1 do return none
  let some ty := matching[0]? | return none
  let some shape := (ty.getObjVal? "shape").toOption | return none
  unless ((shape.getObjValAs? String "kind").toOption == some "dynamic_trait_object") do return none
  return ((shape.getObjVal? "predicates").bind Json.getArr?).toOption

private def compilerBuiltinDerefType? (j : Json) (typeId : Nat) : Option Nat := Id.run do
  let some types := (((j.getObjVal? "types").bind Json.getArr?).toOption) | return none
  let matching := types.filter fun ty =>
    ((ty.getObjValAs? Nat "type_id").toOption == some typeId)
  unless matching.size == 1 do return none
  let some ty := matching[0]? | return none
  let some facts := (ty.getObjVal? "compiler_facts").toOption | return none
  let some queries := (facts.getObjVal? "type_queries").toOption | return none
  let some query := (queries.getObjVal? "builtin_deref_explicit").toOption | return none
  unless ((query.getObjValAs? String "status").toOption == some "supported") do return none
  let some value := (query.getObjVal? "value").toOption | return none
  return jsonTypeId? value

private def exactLockstepTails? (j : Json) (source target : Nat) : Option Json := Id.run do
  let some rows := (((j.getObjVal? "compiler_cast_queries").bind Json.getArr?).toOption) | return none
  let matching := rows.filter fun row =>
    ((row.getObjValAs? String "query_kind").toOption == some "lockstep_tails") &&
    ((row.getObjValAs? String "typing_env").toOption == some "fully_monomorphized") &&
    ((row.getObjValAs? String "status").toOption == some "supported") &&
    ((row.getObjVal? "input_source").toOption.bind jsonTypeId? == some source) &&
    ((row.getObjVal? "input_target").toOption.bind jsonTypeId? == some target)
  unless matching.size == 1 do return none
  return matching[0]?

private def castOperandTypeId? (node : Json) : Option Nat := Id.run do
  let some operand := (node.getObjVal? "operand").toOption | return none
  let some operandKind := ((operand.getObjVal? "kind").bind Json.getStr?).toOption | return none
  if operandKind == "Copy" || operandKind == "Move" then
    let some place := (operand.getObjVal? "place").toOption | return none
    let some ty := (place.getObjVal? "type").toOption | return none
    return jsonTypeId? ty
  else if operandKind == "Constant" then
    let some constant := (operand.getObjVal? "constant").toOption | return none
    let some ty := (constant.getObjVal? "type").toOption | return none
    return jsonTypeId? ty
  else return none

/-- The exporter may retain its salt-zero CTFE vtable probe as diagnostic
evidence, but it is not a runtime allocation identity. Only the exact probe
leaf attached to a supported concrete Unsize Cast and backed by a supported
exact-pair query is demand-local. The enclosing Cast must itself be supported;
all other statuses and descendants remain structural blockers. -/
def exactVtableProbeDiagnostic (j : Json) (path : String) : Bool := Id.run do
  let suffix := ".vtable_probe.status"
  unless path.endsWith suffix do return false
  let castPath := (path.dropEnd suffix.length).toString
  let some node := jsonAtPath j castPath | return false
  unless ((node.getObjValAs? String "status").toOption == some "supported") do return false
  unless ((node.getObjValAs? String "kind").toOption == some "Cast") do return false
  let some castKind := (node.getObjVal? "cast_kind").toOption | return false
  unless ((castKind.getObjValAs? String "status").toOption == some "supported") &&
      ((castKind.getObjValAs? String "kind").toOption == some "PointerCoercion") do return false
  let some coercion := (castKind.getObjVal? "coercion").toOption | return false
  unless ((coercion.getObjValAs? String "kind").toOption == some "Unsize") do return false
  let some sourceType := (node.getObjVal? "target_type").toOption | return false
  let some sourceTypeId := jsonTypeId? sourceType | return false
  unless castOperandTypeId? node |>.isSome do return false
  let some operandTypeId := castOperandTypeId? node | return false
  let some queryRef := (node.getObjVal? "vtable_query").toOption | return false
  unless ((queryRef.getObjValAs? String "status").toOption == some "supported") do return false
  let some queryId := ((queryRef.getObjVal? "query_id").bind Json.getNat?).toOption | return false
  let some querySource := (queryRef.getObjVal? "source_type").toOption | return false
  let some queryTarget := (queryRef.getObjVal? "target_type").toOption | return false
  unless jsonTypeId? querySource == some operandTypeId && jsonTypeId? queryTarget == some sourceTypeId do return false
  let some sourcePointee := (queryRef.getObjVal? "source_pointee_type").toOption | return false
  let some targetPointee := (queryRef.getObjVal? "target_pointee_type").toOption | return false
  let some sourcePointeeId := jsonTypeId? sourcePointee | return false
  let some targetPointeeId := jsonTypeId? targetPointee | return false
  unless compilerBuiltinDerefType? j operandTypeId == some sourcePointeeId &&
      compilerBuiltinDerefType? j sourceTypeId == some targetPointeeId do return false
  let some fullLockstep := exactLockstepTails? j operandTypeId sourceTypeId | return false
  let some fullLockstepValue := (fullLockstep.getObjVal? "value").toOption | return false
  unless ((fullLockstepValue.getObjVal? "source_tail").toOption.bind jsonTypeId? == some operandTypeId) &&
      ((fullLockstepValue.getObjVal? "target_tail").toOption.bind jsonTypeId? == some sourceTypeId) do return false
  let some sourceTail := (queryRef.getObjVal? "source_tail_type").toOption | return false
  let some targetTail := (queryRef.getObjVal? "target_tail_type").toOption | return false
  let some sourceTailId := jsonTypeId? sourceTail | return false
  let some targetTailId := jsonTypeId? targetTail | return false
  let some inputType := (queryRef.getObjVal? "input_type").toOption | return false
  let some inputTypeId := jsonTypeId? inputType | return false
  unless inputTypeId == sourceTailId do return false
  let some queryPredicates := ((queryRef.getObjVal? "input_predicates").bind Json.getArr?).toOption | return false
  let some targetPredicates := dynamicPredicateArray? j targetTailId | return false
  unless targetPredicates == queryPredicates do return false
  let some lockstep := exactLockstepTails? j sourcePointeeId targetPointeeId | return false
  let some lockstepValue := (lockstep.getObjVal? "value").toOption | return false
  unless ((lockstepValue.getObjVal? "source_tail").toOption.bind jsonTypeId? == some sourceTailId) &&
      ((lockstepValue.getObjVal? "target_tail").toOption.bind jsonTypeId? == some targetTailId) do return false
  let some rows := (((j.getObjVal? "compiler_vtable_queries").bind Json.getArr?).toOption) | return false
  let matching := rows.filter fun row =>
    ((row.getObjValAs? Nat "query_id").toOption == some queryId)
  unless matching.size == 1 do return false
  let some row := matching[0]? | return false
  unless ((row.getObjValAs? String "status").toOption == some "supported") do return false
  unless ((row.getObjVal? "input_type").toOption.bind jsonTypeId? == some inputTypeId) do return false
  unless jsonTypeId? ((row.getObjVal? "output_type").toOption.getD .null) |>.isSome do return false
  let some rowInputPredicates := ((row.getObjVal? "input_predicates").bind Json.getArr?).toOption | return false
  unless rowInputPredicates == queryPredicates do return false
  unless ((row.getObjVal? "output_predicates").bind Json.getArr?).isOk do return false
  unless ((row.getObjValAs? Bool "output_type_monomorphic_enough").toOption == some true) &&
      ((row.getObjValAs? Bool "output_predicates_monomorphic_enough").toOption == some true) do return false
  let some probe := (node.getObjVal? "vtable_probe").toOption | return false
  unless ((probe.getObjValAs? String "status").toOption == some "incomplete") &&
      ((probe.getObjValAs? String "kind").toOption == some "symbolic_vtable_allocation") &&
      (((probe.getObjValAs? String "salt_policy").toOption.getD "").startsWith
        "exporter uses CTFE_ALLOC_SALT; Miri runtime allocation salts may be randomized") do return false
  unless (node.getObjVal? "vtable_allocation").toOption == some .null do return false
  unless (match probe.getObjVal? "allocation" with | .error _ => true | .ok _ => false) &&
      (match probe.getObjVal? "allocation_id" with | .error _ => true | .ok _ => false) do return false
  return true

/-- A dynamic-to-dynamic Unsize is represented by the runtime source-vtable
operation. Bind its descriptor to the Cast's complete types, both exact
lockstep queries, and the compiler's fully-monomorphized supertrait-slot row.
This validates evidence identity only; the runtime still obtains the table
from the actual source operand. -/
private def castUnsizingPointeeType? (j : Json) (typeId : Nat) : Option Nat := Id.run do
  let some types := (((j.getObjVal? "types").bind Json.getArr?).toOption) | return none
  let matching := types.filter fun ty => (ty.getObjValAs? Nat "type_id").toOption == some typeId
  unless matching.size == 1 do return none
  let some ty := matching[0]? | return none
  let some shape := (ty.getObjVal? "shape").toOption | return none
  let some kind := (shape.getObjValAs? String "kind").toOption | return none
  if kind == "reference" || kind == "raw_pointer" then
    return (shape.getObjVal? "pointee").toOption.bind jsonTypeId?
  else
    return some typeId

private def exactDynamicVtableUpcast? (j node descriptor : Json) : Bool := Id.run do
  unless ((node.getObjValAs? String "status").toOption == some "supported") &&
      ((node.getObjValAs? String "kind").toOption == some "Cast") do return false
  let some castKind := (node.getObjVal? "cast_kind").toOption | return false
  unless ((castKind.getObjValAs? String "status").toOption == some "supported") &&
      ((castKind.getObjValAs? String "kind").toOption == some "PointerCoercion") do return false
  let some coercion := (castKind.getObjVal? "coercion").toOption | return false
  unless (coercion.getObjValAs? String "kind").toOption == some "Unsize" do return false
  unless ((descriptor.getObjValAs? String "status").toOption == some "supported") &&
      ((descriptor.getObjValAs? String "kind").toOption == some "dynamic_vtable_upcast") do return false
  let some sourceType := (descriptor.getObjVal? "source_type").toOption | return false
  let some sourceTypeId := jsonTypeId? sourceType | return false
  let some targetType := (descriptor.getObjVal? "target_type").toOption | return false
  let some targetTypeId := jsonTypeId? targetType | return false
  unless castOperandTypeId? node == some sourceTypeId do return false
  unless ((node.getObjVal? "target_type").toOption.bind jsonTypeId?) == some targetTypeId do return false

  let some sourcePointee := (descriptor.getObjVal? "source_pointee_type").toOption | return false
  let some sourcePointeeId := jsonTypeId? sourcePointee | return false
  let some targetPointee := (descriptor.getObjVal? "target_pointee_type").toOption | return false
  let some targetPointeeId := jsonTypeId? targetPointee | return false
  unless castUnsizingPointeeType? j sourceTypeId == some sourcePointeeId &&
      castUnsizingPointeeType? j targetTypeId == some targetPointeeId do return false

  let some fullLockstep := exactLockstepTails? j sourceTypeId targetTypeId | return false
  let some fullValue := (fullLockstep.getObjVal? "value").toOption | return false
  let some fullSourceTail := ((fullValue.getObjVal? "source_tail").toOption.bind jsonTypeId?) | return false
  let some fullTargetTail := ((fullValue.getObjVal? "target_tail").toOption.bind jsonTypeId?) | return false
  unless fullSourceTail == sourceTypeId && fullTargetTail == targetTypeId do return false

  let some sourcePointeeLockstep := exactLockstepTails? j sourcePointeeId targetPointeeId | return false
  let some pointeeValue := (sourcePointeeLockstep.getObjVal? "value").toOption | return false
  let some sourceTail := (descriptor.getObjVal? "source_tail_type").toOption | return false
  let some sourceTailId := jsonTypeId? sourceTail | return false
  let some targetTail := (descriptor.getObjVal? "target_tail_type").toOption | return false
  let some targetTailId := jsonTypeId? targetTail | return false
  unless ((pointeeValue.getObjVal? "source_tail").toOption.bind jsonTypeId?) == some sourceTailId &&
      ((pointeeValue.getObjVal? "target_tail").toOption.bind jsonTypeId?) == some targetTailId do return false
  unless (dynamicPredicateArray? j sourceTailId).isSome &&
      (dynamicPredicateArray? j targetTailId).isSome do return false

  unless (descriptor.getObjValAs? String "runtime_vtable").toOption ==
      some "source_operand_metadata" do return false
  let some embeddedQuery := (descriptor.getObjVal? "supertrait_slot_query").toOption | return false
  unless ((embeddedQuery.getObjValAs? String "status").toOption == some "supported") &&
      ((embeddedQuery.getObjValAs? String "query_kind").toOption == some "supertrait_slot") &&
      ((embeddedQuery.getObjValAs? String "typing_env").toOption == some "fully_monomorphized") &&
      ((embeddedQuery.getObjVal? "input_source").toOption.bind jsonTypeId? == some sourceTailId) &&
      ((embeddedQuery.getObjVal? "input_target").toOption.bind jsonTypeId? == some targetTailId) do return false
  let some rows := (((j.getObjVal? "compiler_cast_queries").bind Json.getArr?).toOption) | return false
  let matching := rows.filter fun row =>
    ((row.getObjValAs? String "query_kind").toOption == some "supertrait_slot") &&
    ((row.getObjValAs? String "typing_env").toOption == some "fully_monomorphized") &&
    ((row.getObjValAs? String "status").toOption == some "supported") &&
    ((row.getObjVal? "input_source").toOption.bind jsonTypeId? == some sourceTailId) &&
    ((row.getObjVal? "input_target").toOption.bind jsonTypeId? == some targetTailId)
  unless matching.size == 1 do return false
  let some row := matching[0]? | return false
  unless (match row.getObjVal? "value" with
    | .ok .null => true
    | .ok value => (value.getNat?).isOk
    | .error _ => false) do return false
  return true

private partial def malformedDynamicVtableUpcastAux (root : Json) (node : JsonTraversalCache.Node) (path : String)
    (visited : Std.HashSet JsonTraversalCache.IdentityKey) : Option String × Std.HashSet JsonTraversalCache.IdentityKey := Id.run do
  let current := node.value
  let memoKey := node.identity
  match current with
  | .obj _ | .arr _ => pure ()
  | _ => return (none, visited)
  if node.shouldMemo && visited.contains memoKey then return (none, visited)
  let mut visited := if node.shouldMemo then visited.insert memoKey else visited
  match current with
  | .obj fields =>
    if (current.getObjValAs? String "kind").toOption == some "Cast" then
      if let some descriptor := (current.getObjVal? "vtable_allocation").toOption then
        if (descriptor.getObjValAs? String "kind").toOption == some "dynamic_vtable_upcast" &&
            (descriptor.getObjValAs? String "status").toOption == some "supported" &&
            !exactDynamicVtableUpcast? root current descriptor then
          return (some (joinPath path "vtable_allocation"), visited)
    for ((key, value), childIndex) in fields.toList.zipIdx do
      let (badPath?, nextVisited) := malformedDynamicVtableUpcastAux root (node.child childIndex value) (joinPath path key) visited
      visited := nextVisited
      if let some badPath := badPath? then return (some badPath, visited)
  | .arr values =>
    for (value, childIndex) in values.toList.zipIdx do
      let (badPath?, nextVisited) := malformedDynamicVtableUpcastAux root (node.child childIndex value) s!"{path}[{childIndex}]" visited
      visited := nextVisited
      if let some badPath := badPath? then return (some badPath, visited)
  | _ => pure ()
  return (none, visited)

private def malformedDynamicVtableUpcast? (node : JsonTraversalCache.Node) : Option String :=
  (malformedDynamicVtableUpcastAux node.value node "$" {}).1

private partial def hasFailedStatusAt (j : Json) (wanted path : String) : Bool := Id.run do
  match j with
  | .obj fields =>
    if (j.getObjValAs? String "status").toOption == some "debug_payload" then return false
    if path == wanted then
      if let some status := (j.getObjValAs? String "status").toOption then
        if status != "supported" then return true
    for (key, value) in fields.toList do
      let child := joinPath path key
      if pathCanReach wanted child && hasFailedStatusAt value wanted child then return true
  | .arr values =>
    for (value, index) in values.toList.zipIdx do
      let child := s!"{path}[{index}]"
      if pathCanReach wanted child && hasFailedStatusAt value wanted child then return true
  | _ => pure ()
  return false

/-- Copied catalog diagnostics inherit only their exact original query role.
The original obligations remain present; runtime providers still reject failed
queries when the corresponding source operation requests them. -/
private def retainedQueryDiagnosticRole (j : Json) (path : String) : QueryDependencyRole := Id.run do
  let pathPrefix := "$.selected_scope.retained_catalog_obligations["
  let suffix := "].status"
  unless path.startsWith pathPrefix && path.endsWith suffix do return .structural
  let indexText := ((path.drop pathPrefix.length).dropEnd suffix.length).toString
  let .ok index := decimalNat indexText path | return .structural
  unless toString index == indexText do return .structural
  let some records := (((j.getObjVal? "selected_scope").bind fun scope =>
      (scope.getObjVal? "retained_catalog_obligations").bind Json.getArr?).toOption)
    | return .structural
  let some record := records[index]? | return .structural
  let some sourcePath := ((record.getObjVal? "path").bind Json.getStr?).toOption
    | return .structural
  unless hasFailedStatusAt j ("$." ++ sourcePath) "$" do return .structural
  if exactVtableProbeDiagnostic j ("$." ++ sourcePath ++ ".status") then return .runtimeCast
  return queryDependencyRole ("$." ++ sourcePath ++ ".status")

/-- Return exactly the selected-scope obligations that the readiness gate
blocks on. Keep diagnostics and the execution decision on this single
predicate so reports cannot drift from the fail-closed gate. -/
private def selectedScopeBlockingObligations (j : Json) (obligations : Array Obligation)
    (requiredLayoutPaths : List String) (requiredInstancePaths : Array String) : Array Obligation :=
  obligations.filter fun issue =>
    (!globalCompletenessPath issue.path && !exactVtableProbeDiagnostic j issue.path &&
      obligationQueryRole issue.path == .structural &&
      retainedQueryDiagnosticRole j issue.path == .structural
      || issue.path == "$.selected_scope.kind" || issue.path == "$.selected_scope.status" ||
      issue.path == "$.selected_scope.semantics" || issue.path.startsWith "$.selected_scope.roots[" ||
      requiredLayoutPaths.contains issue.path ||
      requiredInstancePaths.contains issue.path)

private inductive ParsedDocument where
  | full (result : DecodeResult)
  | runtime (result : RuntimeDecodeResult)

private def parseTypeArray (values : Array Json) (memo : DecodeMemo) : Except String (Array TypeNode) := do
  let mut result := #[]
  let mut index := 0
  for value in values do
    result := result.push (← parseTypeNode value s!"$.types[{index}]" memo)
    index := index + 1
  pure result

private def parseAllocationArray (values : Array Json) : Except String (Array AllocationNode) := do
  let mut result := #[]
  let mut index := 0
  for value in values do
    result := result.push (← parseAllocation value s!"$.allocations[{index}]")
    index := index + 1
  pure result

private def parseInstanceArray (values : Array Json) : Except String (Array InstanceNode) := do
  let mut result := #[]
  let mut index := 0
  for value in values do
    result := result.push (← parseInstance value s!"$.instances[{index}]")
    index := index + 1
  pure result

private def parseBodyArray (values : Array Json) (memo : DecodeMemo) : Except String (Array Body) := do
  let mut result := #[]
  let mut index := 0
  for value in values do
    let fallback := match optionalField value "def_path" with
      | some (.str name) => name
      | _ => s!"body[{index}]"
    result := result.push (← parseBody value s!"$.bodies[{index}]" fallback memo)
    index := index + 1
  pure result

private def parseDocument (input : Json) (runtimeOnly : Bool := false)
    (profile : Options := {}) (cachedTraversal : Bool := true) : Except String ParsedDocument := do
  let (resolved,traversal) ← profileit "decoder.shared_payload_resolution" profile fun _ =>
    JsonTraversalCache.resolve input cachedTraversal profile
  let j := resolved.root
  let memo := profileit "decoder.shared_decode_memo" profile fun _ => sharedDecodeMemo resolved.nodes
  if (← fieldString j "schema" "$") != expectedSchema then
    throw s!"$.schema: expected `{expectedSchema}`"
  if (← fieldNat j "schema_version" "$") != expectedSchemaVersion then
    throw s!"$.schema_version: unsupported schema version"
  if let some path := profileit "decoder.dynamic_vtable_scan" profile fun _ =>
      malformedDynamicVtableUpcast? traversal then
    throw s!"{path}: supported dynamic vtable upcast lacks matching compiler cast evidence"
  let producerJson ← field j "producer" "$"
  let producer : Producer := {
    miriCommit := ← fieldString producerJson "miri_commit" "$.producer"
    rustcCommit := ← fieldString producerJson "rustc_commit" "$.producer"
    rustcVersion := ← fieldString producerJson "rustc_version" "$.producer"
    targetTriple := ← fieldString producerJson "target_triple" "$.producer"
  }
  if producer.miriCommit != expectedMiriCommit then throw "$.producer.miri_commit: input is from the wrong pinned Miri revision"
  if producer.rustcCommit != expectedRustcCommit then throw "$.producer.rustc_commit: input is from the wrong pinned rustc revision"
  let completeness ← field j "completeness" "$"
  let completeStatus ← fieldString completeness "status" "$.completeness"
  if !(← fieldBool completeness "unsupported_payloads_are_explicit" "$.completeness") then
    throw "$.completeness.unsupported_payloads_are_explicit: must be true"
  let typesJson ← arrayField j "types" "$"
  if typesJson.isEmpty then throw "$.types: input has no type graph; refusing an empty import"
  let types ← profileit "decoder.types" profile fun _ => parseTypeArray typesJson memo
  let allocationsJson ← arrayField j "allocations" "$"
  let allocations ← profileit "decoder.allocations" profile fun _ => parseAllocationArray allocationsJson
  let compilerAllocIdWorld ← profileit "decoder.compiler_alloc_id_world" profile fun _ => do
    match optionalJson j "compiler_alloc_id_world" with
    | none => pure none
    | some value => pure (some (← parseCompilerAllocIdWorld value allocations))
  let instancesJson ← arrayField j "instances" "$"
  let instances ← profileit "decoder.instances" profile fun _ => parseInstanceArray instancesJson
  let selectedScope ← match optionalJson j "selected_scope" with
    | none => pure none
    | some value => pure (some (← parseSelectedScope value "$.selected_scope"))
  let compilerFunctionAbiTable := profileit "decoder.compiler_abi_queries" profile fun _ =>
    prepareCompilerFunctionAbiTableUsing resolved.nodes memo
  let memo := compilerFunctionAbiTable.extendDecodeMemo memo
  let functionAbis ← profileit "decoder.function_abis" profile fun _ => collectFunctionAbis traversal "$" memo
  let compilerAbiLayoutSchema ← optionalString j "compiler_abi_layout_schema" "$"
  if let some schema := compilerAbiLayoutSchema then
    if schema != expectedCompilerAbiLayoutSchema then
      throw s!"$.compiler_abi_layout_schema: unsupported schema `{schema}`"
    for (abi, abiIndex) in functionAbis.toList.zipIdx do
      for (argument, abiArgumentIndex) in (abi.arguments.push abi.returnValue).toList.zipIdx do
        if argument.layout.isNone then
          throw s!"$.compiler_abi_layout_schema: ABI record {abiIndex} argument {abiArgumentIndex} lacks its physical layout"
  let bodiesJson ← arrayField j "bodies" "$"
  if bodiesJson.isEmpty then throw "$.bodies: input has no MIR bodies; refusing an empty import"
  let bodies ← profileit "decoder.bodies" profile fun _ => parseBodyArray bodiesJson memo
  let typeIds := jsonToNatArray types (·.id)
  let allocationIds := jsonToNatArray allocations (·.id)
  let instanceIds := jsonToNatArray instances (·.id)
  profileit "decoder.validate_dense_type_ids" profile fun _ => validateDense typeIds "type IDs"
  profileit "decoder.validate_dense_allocation_ids" profile fun _ => validateDense allocationIds "allocation IDs"
  profileit "decoder.validate_dense_instance_ids" profile fun _ => validateDense instanceIds "instance IDs"
  profileit "decoder.validate_all_bodies" profile fun _ => validateAllBodies traversal "$"
  profileit "decoder.validate_references" profile fun _ =>
    validateReferences traversal "$" types.size allocations.size instances.size
  let (typedTree?, valueIssues) ← if runtimeOnly then
      let decoded ← profileit "decoder.runtime_value" profile fun _ =>
        decodeRuntimeValue traversal "$" .any .none memo
      pure (none, flattenRuntimeObligations decoded.obligations)
    else
      let typedTree ← decodeValue j "$" .any .none memo
      pure (some typedTree, valueObligations typedTree "$")
  let mut obligations := valueIssues
  obligations := obligations ++ profileit "decoder.extra_semantic_obligations" profile fun _ =>
    extraSemanticObligations j types allocations instances functionAbis bodies
  let requiredDependencies := profileit "decoder.required_dependencies" profile fun _ =>
    requiredStructuralDependencies j compilerAllocIdWorld.isSome
  obligations := profileit "decoder.prepared_world_readiness" profile fun _ =>
    preparedWorldReadinessObligations obligations compilerAllocIdWorld allocations
      requiredDependencies.allocationIds
  obligations := obligations ++ profileit "decoder.required_instance_obligations" profile fun _ =>
    requiredIdentityOnlyInstanceObligations instances requiredDependencies.instanceIds
  obligations := obligations ++ profileit "decoder.thread_local_obligations" profile fun _ =>
    threadLocalShapeObligations requiredDependencies.threadLocalRefs
  match selectedScope with
  | some scope => obligations := obligations ++ profileit "decoder.selected_scope_obligations" profile fun _ =>
      selectedScopeObligations scope bodies instances
  | none => pure ()
  let unresolved ← arrayField completeness "unresolved_obligations" "$.completeness"
  if completeStatus != "complete" then
    let message := if completeStatus == "incomplete" then
        "exporter marked the graph incomplete; this import cannot form executable input"
      else s!"unrecognized completeness status `{completeStatus}`"
    obligations := obligations.push ⟨"$.completeness.status", message⟩
  for (message, obligationIndex) in unresolved.toList.zipIdx do
    match message.getStr? with
    | .ok text => obligations := obligations.push ⟨s!"$.completeness.unresolved_obligations[{obligationIndex}]", text⟩
    | .error _ => throw s!"$.completeness.unresolved_obligations[{obligationIndex}]: expected string"
  let runtimeTargetDataLayout ← match optionalJson j "runtime_target_data_layout" with
    | none => pure none
    | some evidence => pure (some ({
        status := parseStatus (← fieldString evidence "status" "$.runtime_target_data_layout")
        payload := evidence
      } : TargetDataLayoutEvidence))
  let core : ImportDocumentCore := {
    compilerPredicates := ← match optionalField j "compiler_predicate_queries" with
      | none => pure #[]
      | some value => (← value.getArr?).mapM decodeCompilerPredicateEvidence
    compilerAbiLayoutSchema := compilerAbiLayoutSchema
    producer := producer
    runtimeTargetDataLayout := runtimeTargetDataLayout
    completenessStatus := parseStatus completeStatus
    types := types
    allocations := allocations
    compilerAllocIdWorld := compilerAllocIdWorld
    instances := instances
    selectedScope := selectedScope
    functionAbis := functionAbis
    bodies := bodies
    obligations := obligations
    raw := j
    sharedNodes := resolved.nodes
    compilerFunctionAbiTable := some compilerFunctionAbiTable
    compilerValueMemo := if runtimeOnly then some (profileit "decoder.compiler_values" profile fun _ =>
      prepareCompilerValueMemoUsing resolved.nodes memo) else none
  }
  let requiredLayoutPaths := types.toList.zipIdx.filterMap fun (ty, typeIndex) =>
    if requiredDependencies.typeIds.contains ty.id then some s!"$.types[{typeIndex}].layout.status" else none
  let requiredInstancePaths := instances.toList.zipIdx.foldl (fun paths (instNode, instanceIndex) =>
    if requiredDependencies.instanceIds.contains instNode.id then
      paths ++ #[s!"instances[{instanceIndex}]", s!"$.instances[{instanceIndex}].status"]
    else paths) #[]
  let scopeIsSelected := selectedScope.isSome
  let blockingObligations := if scopeIsSelected then
      selectedScopeBlockingObligations j obligations requiredLayoutPaths requiredInstancePaths
    else obligations
  let scopeIssuesRemain := !blockingObligations.isEmpty
  let ready :=
    if scopeIsSelected then !scopeIssuesRemain
    else completeStatus == "complete" && obligations.isEmpty
  match typedTree? with
  | some typedTree =>
    let doc := core.withTypedTree typedTree
    let executionInput := if ready then some ⟨doc⟩ else none
    return .full ⟨doc, executionInput, blockingObligations⟩
  | none =>
    let executionInput := if ready then some ⟨core⟩ else none
    return .runtime ⟨core, executionInput, blockingObligations⟩

def decodeJson (text : String) : Except String DecodeResult := do
  let json ← Json.parse text
  match ← parseDocument json with
  | .full result => pure result
  | .runtime _ => throw "internal decoder mode mismatch"

def decodeFile (path : System.FilePath) : IO (Except String DecodeResult) := do
  try
    let text ← IO.FS.readFile path
    pure (decodeJson text)
  catch error => pure (.error s!"could not read {path}: {error}")

/-- Runtime decoder with optional Lean profiler options. Profiling wrappers are
kernel identity functions; with profiling disabled this preserves the ordinary
decoder result and diagnostic order. -/
def decodeRuntimeJsonProfiled (text : String) (profile : Options) : Except String RuntimeDecodeResult := do
  let json ← profileit "decoder.json_parse" profile fun _ => Json.parse text
  match ← profileit "decoder.document" profile fun _ => parseDocument json true profile with
  | .runtime result => pure result
  | .full _ => throw "internal decoder mode mismatch"

/-- Regression oracle: identical validation with the structural-hash memo off.
This is not a relaxed decoder and retains the full original error ordering. -/
def decodeRuntimeJsonReference (text : String) : Except String RuntimeDecodeResult := do
  let json ← Json.parse text
  match ← parseDocument json true {} false with
  | .runtime result => pure result
  | .full _ => throw "internal decoder mode mismatch"

def decodeJsonReference (text : String) : Except String DecodeResult := do
  let json ← Json.parse text
  match ← parseDocument json false {} false with
  | .full result => pure result
  | .runtime _ => throw "internal decoder mode mismatch"

/-- Runtime-only entry point, preserving validation and diagnostic precedence
without retaining the full typed projection. -/
def decodeRuntimeJson (text : String) : Except String RuntimeDecodeResult :=
  decodeRuntimeJsonProfiled text {}

def decodeRuntimeFile (path : System.FilePath) : IO (Except String RuntimeDecodeResult) := do
  try
    let text ← IO.FS.readFile path
    pure (decodeRuntimeJson text)
  catch error => pure (.error s!"could not read {path}: {error}")

/-- Typed metadata entrypoints for compiler-query adapters. -/
def decodeAllocationMemoryEvidence (j : Json) : Except String AllocationMemory :=
  parseAllocationMemory j "$allocation"


end Miri.Input
