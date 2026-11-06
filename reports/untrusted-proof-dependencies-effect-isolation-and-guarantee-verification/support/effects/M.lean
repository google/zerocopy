import Lean

open Lean Elab Command Term Tactic

-- 1. Module-level `[init]` / `initialize`
initialize
  IO.println "[M:init-1] regular initialize block executed"

-- 2. Custom PersistentEnvExtension registered via `initialize`
initialize myExt : PersistentEnvExtension Name Name (Array Name) ←
  registerPersistentEnvExtension {
    name := `M.myExt
    mkInitial := do
      IO.println "[M:ext-mkInitial] PersistentEnvExtension.mkInitial executed"
      return #[]
    addImportedFn := fun entries => do
      IO.println s!"[M:ext-addImportedFn] PersistentEnvExtension.addImportedFn executed (modules={entries.size})"
      return #[]
    addEntryFn := Array.push
    exportEntriesFn := id
  }

-- 3. Custom macro: test pure expansion vs. unsafeIO via @[implemented_by]
unsafe def impureHookImpl (s : String) : String :=
  match unsafeIO (do IO.println s!"[M:macro-unsafeIO] executed during MacroM: {s}"; return s ++ "!") with
  | .ok res => res
  | .error _ => ""

@[implemented_by impureHookImpl]
opaque hookedString (s : String) : String := s

syntax (name := mPureMacro) "m_pure_macro" : term
@[macro mPureMacro] def expandMPureMacro : Macro := fun _ => do
  let msg := hookedString "hello from macro expansion"
  `($(quote msg).length)

-- Macro that expands into an effectful `by_elab` term
syntax (name := mTrojanMacro) "m_trojan_macro" : term
macro_rules
  | `(m_trojan_macro) => `(by_elab do
      IO.println "[M:trojan-macro->by_elab] IO executed in TermElabM after macro expansion"
      return mkNatLit 99)

-- 4. Custom command elaborator
syntax (name := mCustomCmd) "#m_custom_cmd" : command

@[command_elab mCustomCmd]
def elabMCustomCmd : CommandElab := fun _ => do
  IO.println "[M:elabMCustomCmd-run] custom command elaborator executed"

-- 5. Custom tactic
syntax (name := mCustomTac) "m_custom_tac" : tactic

@[tactic mCustomTac]
def evalMCustomTac : Tactic := fun _ => do
  IO.println "[M:evalMCustomTac-run] custom tactic executed"
  evalTactic (← `(tactic| trivial))
