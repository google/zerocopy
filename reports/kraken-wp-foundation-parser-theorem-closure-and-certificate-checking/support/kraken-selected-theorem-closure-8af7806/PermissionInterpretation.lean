module
import Kraken.X64.OmniSemantics

def PermissionAll (readable writable : BitVec 64 → Nat → Prop)
    (executable : Std.Rco Int64 → Prop) (post : MachineState → Prop) : Effects → Prop
  | .done s => post s
  | .unimplemented _ => False
  | .gp_unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined _ _ k => ∀ v, PermissionAll readable writable executable post (k v)
  | .require_read_access a w k => readable a w.bytes ∧ PermissionAll readable writable executable post (k ())
  | .require_write_access a w k => writable a w.bytes ∧ PermissionAll readable writable executable post (k ())
  | .require_exec_access p k => executable p ∧ PermissionAll readable writable executable post (k ())

theorem permission_erasure (r w x post) (e : Effects) :
    PermissionAll r w x post e → e.All post := by
  induction e with
  | done => exact id
  | unimplemented => exact id
  | gp_unaligned => exact id
  | nonmem_load => simp [PermissionAll, Effects.All]
  | nonmem_store => simp [PermissionAll, Effects.All]
  | undefined k ih =>
    intro h v
    exact ih v (h v)
  | require_read_access a sz k ih =>
    intro h
    exact ih () h.2
  | require_write_access a sz k ih =>
    intro h
    exact ih () h.2
  | require_exec_access p k ih =>
    intro h
    exact ih () h.2

def noAccess : BitVec 64 → Nat → Prop := fun _ _ => False
def noExec : Std.Rco Int64 → Prop := fun _ => False
def forbiddenRestore : Effects :=
  .require_write_access 4096 .W8 (fun _ =>
  .require_write_access 4096 .W8 (fun _ => .done ⟨{}, 0⟩))

theorem default_accepts_forbiddenRestore : forbiddenRestore.All (fun _ => True) := by trivial
theorem permission_rejects_forbiddenRestore :
    ¬ PermissionAll noAccess noAccess noExec (fun _ => True) forbiddenRestore := by
  intro h
  exact h.1

#print axioms permission_erasure
#print axioms permission_rejects_forbiddenRestore
