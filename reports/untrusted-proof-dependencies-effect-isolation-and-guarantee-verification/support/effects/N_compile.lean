import M

-- Confirm MacroM has no MonadLiftT IO instance while CoreM/MetaM/TermElabM/CommandElabM/TacticM do:
#check (inferInstance : MonadLiftT IO Lean.CoreM)
#check (inferInstance : MonadLiftT IO Lean.MetaM)
#check (inferInstance : MonadLiftT IO Lean.Elab.Term.TermElabM)
#check (inferInstance : MonadLiftT IO Lean.Elab.Command.CommandElabM)
#check (inferInstance : MonadLiftT IO Lean.Elab.Tactic.TacticM)
#check (inferInstance : MonadLiftT IO Lean.AttrM)
#check (inferInstance : MonadLiftT IO Lean.ImportM)

/-- error: failed to synthesize instance of type class
  MonadLiftT IO Lean.MacroM

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. -/
#guard_msgs in
#check (inferInstance : MonadLiftT IO Lean.MacroM)

-- Trigger macro expansion, trojan macro->by_elab, custom command elab, and custom tactic:
def x : Nat := m_pure_macro
def y : Nat := m_trojan_macro
#m_custom_cmd
theorem t : True := by m_custom_tac
