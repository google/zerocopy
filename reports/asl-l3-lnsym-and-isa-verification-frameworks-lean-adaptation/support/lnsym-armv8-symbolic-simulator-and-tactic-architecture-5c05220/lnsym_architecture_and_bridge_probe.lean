/-
  lnsym_architecture_and_bridge_probe.lean

  Standalone Lean 4.34.1 mechanization for:
    "LNSym AArch64 Symbolic Simulator, Tactic Architecture, and Memory
     Framing (`leanprover/LNSym` @ `5c05220`)"

  What this file mechanizes:
  1. Anneal's target refinement and small-step machine contract
     (`Trusted.Refinement` and `Trusted.StepResult`: `Partial`, `Preorder`,
     `Language`, `Compiles`, `FailureKind`, `StepResult`, `SmallStepMachine`,
     `ReachesPrefix`, `BehaviorOf`, `WellFormedOn`).
  2. LNSym's `ArmState` (`Arm/State.lean`), Harvard-style separation of
     `program : List (BitVec 64 × BitVec 32)` from total byte-addressed
     `mem : BitVec 64 → BitVec 8`, unified `StateField` accessor/updater
     (`r` / `w`) read-over-write and write-over-write lemmas, `StateError`,
     `CheckSPAlignment`, and little-endian byte-slice memory operations
     (`Memory.read_bytes` / `Memory.write_bytes`).
  3. LNSym's half-open memory region model (`Arm/Memory/Separate.lean`:
     `mem_legal'`, `mem_separate'`, `mem_subset'`) and machine-checked
     read-over-write framing (`read_bytes_write_bytes_eq_read_bytes_of_mem_separate'`),
     same-region forwarding (`read_bytes_write_bytes_same`), and self-store
     identity (`write_bytes_read_bytes_eq`).
  4. LNSym's word-level decoder (`decode_raw_inst : BitVec 32 → Option ArmInst`),
     single-step/multi-step evaluators (`stepi`, `run`), and concrete proofs
     witnessing the two primary-source bugs in `Arm/Decode.lean`:
     - `LDST.mayModifiedRegs` (`Arm/Decode.lean:260-308`) inverts the load/store
       polarity (`opc[0]` / `L`), reporting `[]` for `LDR` and `[Rt, Rn]` for
       `STR`.
     - `BR.mayModifiedRegs` (`Arm/Decode.lean:103-109`) unconditionally returns
       `[]`, omitting `x30` (`LR`) on `BL`.
  5. Negative control: Because LNSym's `ArmState` uses a total byte memory
     `BitVec 64 → BitVec 8` and emits no memory-access event trace, a dead
     unauthorized load (`ldr x2, [x0, #8]` followed by overwriting `x2`) and
     a self-store to an unauthorized address (`ldr x2, [x0, #8]; str x2, [x0, #8]`)
     produce the exact same final `ArmState` (with `error = .None` and
     extensionally equal `mem` by `funext`) as a valid 8-byte swap leaf.
  6. Positive bridge: Wrapping LNSym's `stepi` with an instruction-level
     access-footprint observer (`instMemAccesses`) into Anneal's
     `SmallStepMachine` accepts the valid 8-byte swap leaf and proves end-to-end
     `Compiles` refinement, while rejecting both the dead out-of-bounds load
     and the unauthorized self-store with `.failed .ub`.
-/

namespace LNSymArchitectureAndBridgeProbe

/-! ## Section 1: Anneal Target Refinement & Small-Step Machine Contract -/

class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

def Partial.map {B₁ : Type u} {B₂ : Type v} (f : B₁ → B₂) (p : Partial B₁) :
    Partial B₂ where
  defined := p.defined
  val h := f (p.val h)

instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

abbrev Language.Behavior (L : Language) : Type :=
  LNSymArchitectureAndBridgeProbe.Behavior L.Query L.Out

def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

inductive FailureKind where
  | ub
  | error
  deriving DecidableEq, Repr

inductive StepResult (State Obs : Type) where
  | stepped (next : State)
  | halted (obs : Obs)
  | failed (kind : FailureKind)
  deriving DecidableEq, Repr

structure SmallStepMachine (State Obs : Type) where
  step : State → StepResult State Obs

inductive ReachesPrefix (M : SmallStepMachine State Obs) :
    Nat → State → StepResult State Obs → Prop where
  | zero (s : State) :
      ReachesPrefix M 0 s (M.step s)
  | succ {n : Nat} {s s' : State} {r : StepResult State Obs} :
      M.step s = .stepped s' →
      ReachesPrefix M n s' r →
      ReachesPrefix M (n + 1) s r

theorem ReachesPrefix.deterministic {M : SmallStepMachine State Obs}
    {n : Nat} {s : State} {r₁ r₂ : StepResult State Obs}
    (h₁ : ReachesPrefix M n s r₁) (h₂ : ReachesPrefix M n s r₂) :
    r₁ = r₂ := by
  induction h₁ generalizing r₂ with
  | zero s =>
    cases h₂ with
    | zero => rfl
  | succ hstep _ ih =>
    cases h₂ with
    | succ hstep' hrest' =>
      rw [hstep] at hstep'
      injection hstep' with hss
      subst hss
      exact ih hrest'

theorem ReachesPrefix.TerminalNoStepFurther {M : SmallStepMachine State Obs}
    {n₁ n₂ : Nat} {s : State} {r₁ r₂ : StepResult State Obs}
    (h₁ : ReachesPrefix M n₁ s r₁)
    (hterm : ∀ s', r₁ ≠ .stepped s')
    (h₂ : ReachesPrefix M n₂ s r₂)
    (hle : n₁ ≤ n₂) :
    n₁ = n₂ ∧ r₁ = r₂ := by
  induction h₁ generalizing n₂ r₂ with
  | zero s =>
    cases h₂ with
    | zero => exact ⟨rfl, rfl⟩
    | succ hstep _ => exact False.elim (hterm _ hstep)
  | succ hstep _ ih =>
    cases h₂ with
    | zero => omega
    | succ hstep' hrest' =>
      rw [hstep] at hstep'
      injection hstep' with hss
      subst hss
      have ⟨heq, hreq⟩ := ih hterm hrest' (by omega)
      exact ⟨by omega, hreq⟩

def BehaviorOf (M : SmallStepMachine State Obs) (s₀ : State) : Partial (Obs → Prop) where
  defined := ∀ n, ¬ ReachesPrefix M n s₀ (.failed .ub)
  val := fun _ obs => ∃ n, ReachesPrefix M n s₀ (.halted obs)

/-! ## Section 2: LNSym `ArmState`, Harvard Split, and `r`/`w` Algebra (`Arm/State.lean`) -/

abbrev Store (α : Type) (β : Type) := α → β

def write [DecidableEq α] (s : Store α β) (a : α) (b : β) : Store α β :=
  fun x => if x = a then b else s x

inductive PFlag where
  | N | Z | C | V
  deriving DecidableEq, Repr

structure PState where
  n : BitVec 1
  z : BitVec 1
  c : BitVec 1
  v : BitVec 1
  deriving DecidableEq, Repr

inductive StateError where
  | None
  | NotFound (pc : BitVec 64)
  | Unimplemented (inst : BitVec 32)
  | Illegal (inst : BitVec 32)
  | Fault (addr : BitVec 64)
  | Other
  deriving DecidableEq, Repr

inductive RegType where
  | GPR : BitVec 5 → RegType
  | SFP : BitVec 5 → RegType
  deriving DecidableEq, Repr

inductive StateField where
  | GPR  : BitVec 5 → StateField
  | SFP  : BitVec 5 → StateField
  | PC   : StateField
  | FLAG : PFlag → StateField
  | ERR  : StateField
  deriving DecidableEq, Repr

abbrev state_value (fld : StateField) : Type :=
  match fld with
  | .GPR _  => BitVec 64
  | .SFP _  => BitVec 128
  | .PC     => BitVec 64
  | .FLAG _ => BitVec 1
  | .ERR    => StateError

abbrev Memory := Store (BitVec 64) (BitVec 8)
abbrev Program := List (BitVec 64 × BitVec 32)

def Program.find? (p : Program) (addr : BitVec 64) : Option (BitVec 32) :=
  match p with
  | [] => none
  | (a, w) :: rest => if a = addr then some w else Program.find? rest addr

structure ArmState where
  gpr     : Store (BitVec 5) (BitVec 64)
  sfp     : Store (BitVec 5) (BitVec 128)
  pc      : BitVec 64
  pstate  : PState
  mem     : Memory
  program : Program
  error   : StateError

def r (fld : StateField) (s : ArmState) : state_value fld :=
  match fld with
  | .GPR i   => s.gpr i
  | .SFP i   => s.sfp i
  | .PC      => s.pc
  | .FLAG .N => s.pstate.n
  | .FLAG .Z => s.pstate.z
  | .FLAG .C => s.pstate.c
  | .FLAG .V => s.pstate.v
  | .ERR     => s.error

def w (fld : StateField) (v : state_value fld) (s : ArmState) : ArmState :=
  match fld with
  | .GPR i   => { s with gpr := write s.gpr i v }
  | .SFP i   => { s with sfp := write s.sfp i v }
  | .PC      => { s with pc := v }
  | .FLAG .N => { s with pstate := { s.pstate with n := v } }
  | .FLAG .Z => { s with pstate := { s.pstate with z := v } }
  | .FLAG .C => { s with pstate := { s.pstate with c := v } }
  | .FLAG .V => { s with pstate := { s.pstate with v := v } }
  | .ERR     => { s with error := v }

@[simp]
theorem r_of_w_same (fld : StateField) (v : state_value fld) (s : ArmState) :
    r fld (w fld v s) = v := by
  cases fld with
  | GPR i => simp [r, w, write]
  | SFP i => simp [r, w, write]
  | PC => rfl
  | FLAG f => cases f <;> rfl
  | ERR => rfl

@[simp]
theorem r_of_w_different {fld₁ fld₂ : StateField} (v : state_value fld₂) (s : ArmState)
    (hne : fld₁ ≠ fld₂) :
    r fld₁ (w fld₂ v s) = r fld₁ s := by
  cases fld₁ <;> cases fld₂
  · rename_i i₁ i₂
    simp only [r, w, write]
    split
    · next h => exact False.elim (hne (by subst h; rfl))
    · rfl
  · rfl
  · rfl
  · rename_i i₁ f₂; cases f₂ <;> rfl
  · rfl
  · rfl
  · rename_i i₁ i₂
    simp only [r, w, write]
    split
    · next h => exact False.elim (hne (by subst h; rfl))
    · rfl
  · rfl
  · rename_i i₁ f₂; cases f₂ <;> rfl
  · rfl
  · rfl
  · rfl
  · exact False.elim (hne rfl)
  · rename_i f₂; cases f₂ <;> rfl
  · rfl
  · rename_i f₁ i₂; cases f₁ <;> rfl
  · rename_i f₁ i₂; cases f₁ <;> rfl
  · rename_i f₁; cases f₁ <;> rfl
  · rename_i f₁ f₂
    cases f₁ <;> cases f₂ <;> first | rfl | exact False.elim (hne rfl)
  · rename_i f₁; cases f₁ <;> rfl
  · rfl
  · rfl
  · rfl
  · rename_i f₂; cases f₂ <;> rfl
  · exact False.elim (hne rfl)

@[simp]
theorem w_of_w_shadow (fld : StateField) (v₁ v₂ : state_value fld) (s : ArmState) :
    w fld v₂ (w fld v₁ s) = w fld v₂ s := by
  cases fld with
  | GPR i =>
    simp only [w, ArmState.mk.injEq, and_true]
    funext x
    simp only [write]
    split <;> rfl
  | SFP i =>
    simp only [w, ArmState.mk.injEq, true_and, and_true]
    funext x
    simp only [write]
    split <;> rfl
  | PC => rfl
  | FLAG f => cases f <;> rfl
  | ERR => rfl

@[simp]
theorem w_program (fld : StateField) (v : state_value fld) (s : ArmState) :
    (w fld v s).program = s.program := by
  cases fld with
  | GPR _ | SFP _ | PC | ERR => rfl
  | FLAG f => cases f <;> rfl

@[simp]
theorem w_mem (fld : StateField) (v : state_value fld) (s : ArmState) :
    (w fld v s).mem = s.mem := by
  cases fld with
  | GPR _ | SFP _ | PC | ERR => rfl
  | FLAG f => cases f <;> rfl

def read_gpr_zr (idx : BitVec 5) (s : ArmState) : BitVec 64 :=
  if idx = 31#5 then 0#64 else r (.GPR idx) s

def write_gpr_zr (idx : BitVec 5) (val : BitVec 64) (s : ArmState) : ArmState :=
  if idx = 31#5 then s else w (.GPR idx) val s

def CheckSPAlignment (s : ArmState) : Bool :=
  BitVec.extractLsb' 0 4 (r (.GPR 31#5) s) == 0#4

def fetch_inst (addr : BitVec 64) (s : ArmState) : Option (BitVec 32) :=
  s.program.find? addr

/-! ### Little-Endian Byte-Slice Memory Operations (`Memory.read_bytes` / `Memory.write_bytes`) -/

namespace Memory

def read_bytes (n : Nat) (addr : BitVec 64) (m : Memory) : BitVec (n * 8) :=
  match n with
  | 0 => 0#0
  | n' + 1 =>
    let byte := m addr
    let rest := read_bytes n' (addr + 1#64) m
    have h : n' * 8 + 8 = (n' + 1) * 8 := by omega
    (rest ++ byte).cast h

def write_bytes (n : Nat) (addr : BitVec 64) (val : BitVec (n * 8)) (m : Memory) : Memory :=
  match n with
  | 0 => m
  | n' + 1 =>
    let byte := BitVec.extractLsb' 0 8 val
    let rest := BitVec.extractLsb' 8 (n' * 8) val
    write_bytes n' (addr + 1#64) rest (write m addr byte)

end Memory

def read_mem_bytes (n : Nat) (addr : BitVec 64) (s : ArmState) : BitVec (n * 8) :=
  Memory.read_bytes n addr s.mem

def write_mem_bytes (n : Nat) (addr : BitVec 64) (val : BitVec (n * 8)) (s : ArmState) : ArmState :=
  { s with mem := Memory.write_bytes n addr val s.mem }

@[simp]
theorem write_mem_bytes_program (n : Nat) (addr : BitVec 64) (val : BitVec (n * 8)) (s : ArmState) :
    (write_mem_bytes n addr val s).program = s.program := rfl

@[simp]
theorem r_of_write_mem_bytes (fld : StateField) (n : Nat) (addr : BitVec 64)
    (val : BitVec (n * 8)) (s : ArmState) :
    r fld (write_mem_bytes n addr val s) = r fld s := by
  cases fld with
  | GPR _ | SFP _ | PC | ERR => rfl
  | FLAG f => cases f <;> rfl

/-! ## Section 3: LNSym Half-Open Memory Region Framing (`Arm/Memory/Separate.lean`) -/

def mem_legal' (a : BitVec 64) (n : Nat) : Prop :=
  a.toNat + n ≤ 2 ^ 64

instance (a : BitVec 64) (n : Nat) : Decidable (mem_legal' a n) :=
  inferInstanceAs (Decidable (a.toNat + n ≤ 2 ^ 64))

structure mem_separate' (a : BitVec 64) (an : Nat) (b : BitVec 64) (bn : Nat) : Prop where
  ha : mem_legal' a an
  hb : mem_legal' b bn
  h  : a.toNat + an ≤ b.toNat ∨ b.toNat + bn ≤ a.toNat

structure mem_subset' (a : BitVec 64) (an : Nat) (b : BitVec 64) (bn : Nat) : Prop where
  ha : mem_legal' a an
  hb : mem_legal' b bn
  h₁ : b.toNat ≤ a.toNat
  h₂ : a.toNat + an ≤ b.toNat + bn

theorem mem_separate'_comm {a b : BitVec 64} {an bn : Nat}
    (h : mem_separate' a an b bn) : mem_separate' b bn a an :=
  ⟨h.hb, h.ha, h.h.symm⟩

theorem toNat_add_one_of_mem_legal' {a : BitVec 64} {n : Nat}
    (h : mem_legal' a (n + 1)) (hn : 0 < n) :
    (a + 1#64).toNat = a.toNat + 1 := by
  unfold mem_legal' at h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem write_bytes_not_in_span (n : Nat) (b x : BitVec 64) (val : BitVec (n * 8)) (m : Memory)
    (hb : mem_legal' b n)
    (hx : x.toNat < b.toNat ∨ b.toNat + n ≤ x.toNat) :
    Memory.write_bytes n b val m x = m x := by
  induction n generalizing b m with
  | zero => rfl
  | succ n' ih =>
    unfold Memory.write_bytes
    have hne : x ≠ b := by
      intro heq
      subst heq
      rcases hx with h | h <;> omega
    by_cases hn' : n' = 0
    · subst hn'
      simp [Memory.write_bytes, write, hne]
    · have hpos : 0 < n' := Nat.pos_of_ne_zero hn'
      have htoNat : (b + 1#64).toNat = b.toNat + 1 := toNat_add_one_of_mem_legal' hb hpos
      have hb' : mem_legal' (b + 1#64) n' := by
        unfold mem_legal' at hb ⊢
        omega
      have hx' : x.toNat < (b + 1#64).toNat ∨ (b + 1#64).toNat + n' ≤ x.toNat := by
        rcases hx with h | h
        · left; omega
        · right; omega
      rw [ih (b + 1#64) _ _ hb' hx']
      simp [write, hne]

/-- LNSym's core disjoint read-over-write framing theorem
    (`Arm/Memory/Separate.lean:537`: `read_bytes_write_bytes_eq_read_bytes_of_mem_separate'`). -/
theorem Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate'
    (an bn : Nat) (a b : BitVec 64) (val : BitVec (bn * 8)) (m : Memory)
    (hsep : mem_separate' a an b bn) :
    Memory.read_bytes an a (Memory.write_bytes bn b val m) = Memory.read_bytes an a m := by
  induction an generalizing a with
  | zero => rfl
  | succ an' ih =>
    unfold Memory.read_bytes
    have hbyte : Memory.write_bytes bn b val m a = m a := by
      apply write_bytes_not_in_span bn b a val m hsep.hb
      rcases hsep.h with h | h
      · left; omega
      · right; omega
    by_cases han' : an' = 0
    · subst han'
      simp [Memory.read_bytes, hbyte]
    · have hpos : 0 < an' := Nat.pos_of_ne_zero han'
      have htoNat : (a + 1#64).toNat = a.toNat + 1 := toNat_add_one_of_mem_legal' hsep.ha hpos
      have hsep' : mem_separate' (a + 1#64) an' b bn := by
        refine ⟨?_, hsep.hb, ?_⟩
        · have hha := hsep.ha
          unfold mem_legal' at hha ⊢
          omega
        · rcases hsep.h with h | h
          · left; omega
          · right; omega
      rw [hbyte, ih (a + 1#64) hsep']

/-- Same-region read-over-write forwarding: reading `n` bytes from `addr` immediately
    after writing `val : BitVec (n * 8)` to `addr` (under `mem_legal' addr n`) returns `val`. -/
theorem Memory.read_bytes_write_bytes_same
    (n : Nat) (addr : BitVec 64) (val : BitVec (n * 8)) (m : Memory)
    (hlegal : mem_legal' addr n) :
    Memory.read_bytes n addr (Memory.write_bytes n addr val m) = val := by
  induction n generalizing addr m with
  | zero =>
    simp only [Memory.read_bytes]
    exact BitVec.eq_nil val |>.symm
  | succ n' ih =>
    unfold Memory.read_bytes Memory.write_bytes
    by_cases hn' : n' = 0
    · subst hn'
      simp only [Memory.read_bytes, Memory.write_bytes, write, ↓reduceIte]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi_lt
      simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
        Nat.zero_add]
      simp [hi_lt]
    · have hpos : 0 < n' := Nat.pos_of_ne_zero hn'
      have htoNat : (addr + 1#64).toNat = addr.toNat + 1 :=
        toNat_add_one_of_mem_legal' hlegal hpos
      have hlegal' : mem_legal' (addr + 1#64) n' := by
        unfold mem_legal' at hlegal ⊢
        omega
      have hbyte : Memory.write_bytes n' (addr + 1#64) (BitVec.extractLsb' 8 (n' * 8) val)
          (write m addr (BitVec.extractLsb' 0 8 val)) addr =
          BitVec.extractLsb' 0 8 val := by
        rw [write_bytes_not_in_span n' (addr + 1#64) addr _ _ hlegal' (by left; omega)]
        simp [write]
      have hrest := ih (addr + 1#64) (BitVec.extractLsb' 8 (n' * 8) val)
        (write m addr (BitVec.extractLsb' 0 8 val)) hlegal'
      rw [hbyte, hrest]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi_lt
      simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
        Nat.zero_add]
      by_cases hi : i < 8
      · simp [hi]
      · have hlt : i - 8 < n' * 8 := by omega
        have hadd : 8 + (i - 8) = i := by omega
        simp [hi, hlt, hadd]

/-- Self-store identity: writing the bytes just read from `[addr, addr + n)` back to
    `[addr, addr + n)` yields the exact same `Memory` function (`funext`). -/
theorem Memory.write_bytes_read_bytes_eq (n : Nat) (addr : BitVec 64) (m : Memory) :
    Memory.write_bytes n addr (Memory.read_bytes n addr m) m = m := by
  induction n generalizing addr m with
  | zero => rfl
  | succ n' ih =>
    unfold Memory.read_bytes Memory.write_bytes
    dsimp only
    have hcast : n' * 8 + 8 = (n' + 1) * 8 := by omega
    have hwrite : write m addr (BitVec.extractLsb' 0 8
        ((Memory.read_bytes n' (addr + 1#64) m ++ m addr).cast hcast)) = m := by
      funext x
      simp only [write]
      split
      · next h =>
        subst h
        apply BitVec.eq_of_getLsbD_eq
        intro i hi_lt
        simp only [BitVec.getLsbD_extractLsb', Nat.zero_add,
          BitVec.getLsbD_cast, BitVec.getLsbD_append]
        simp [hi_lt]
      · rfl
    have hrest : BitVec.extractLsb' 8 (n' * 8)
        ((Memory.read_bytes n' (addr + 1#64) m ++ m addr).cast hcast) =
        Memory.read_bytes n' (addr + 1#64) m := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi_lt
      simp only [BitVec.getLsbD_extractLsb',
        BitVec.getLsbD_cast, BitVec.getLsbD_append]
      have hge : ¬ (8 + i < 8) := by omega
      simp [hi_lt, hge]
    rw [hwrite, hrest]
    exact ih (addr + 1#64) m

/-! ## Section 4: Word-Level Decoding (`decode_raw_inst`), `mayModifiedRegs` Bugs, and `stepi` -/

/-- LNSym's `Reg_imm_cls` (`Arm/Decode/LDST.lean:45-54`):
    Load/store register (unsigned immediate), `[size:2, 111, V:1, 01, opc:2, imm12:12, Rn:5, Rt:5]`. -/
structure Reg_imm_cls where
  size  : BitVec 2
  V     : BitVec 1
  opc   : BitVec 2
  imm12 : BitVec 12
  Rn    : BitVec 5
  Rt    : BitVec 5
  deriving DecidableEq, Repr

/-- LNSym's `Add_sub_imm_cls` (`Arm/Decode/DPI.lean:16-24`):
    Add/subtract (immediate), `[sf:1, op:1, S:1, 100010, sh:1, imm12:12, Rn:5, Rd:5]`. -/
structure Add_sub_imm_cls where
  sf    : BitVec 1
  op    : BitVec 1
  S     : BitVec 1
  sh    : BitVec 1
  imm12 : BitVec 12
  Rn    : BitVec 5
  Rd    : BitVec 5
  deriving DecidableEq, Repr

/-- LNSym's `Uncond_branch_imm_cls` (`Arm/Decode/BR.lean:42-45`):
    Unconditional branch (immediate) `B` / `BL`, `[op:1, 00101, imm26:26]`. -/
structure Uncond_branch_imm_cls where
  op    : BitVec 1
  imm26 : BitVec 26
  deriving DecidableEq, Repr

/-- LNSym's `Uncond_branch_reg_cls` (`Arm/Decode/BR.lean:51-59`):
    Unconditional branch (register) `RET`, `[1101011, opc:4, op2:5, op3:6, Rn:5, op4:5]`. -/
structure Uncond_branch_reg_cls where
  opc : BitVec 4
  op2 : BitVec 5
  op3 : BitVec 6
  Rn  : BitVec 5
  op4 : BitVec 5
  deriving DecidableEq, Repr

inductive ArmInst where
  | LDST_Reg_imm (i : Reg_imm_cls)
  | DPI_Add_sub_imm (i : Add_sub_imm_cls)
  | BR_Uncond_branch_imm (i : Uncond_branch_imm_cls)
  | BR_Uncond_branch_reg (i : Uncond_branch_reg_cls)
  deriving DecidableEq, Repr

/-- Word-level bitfield decoder matching `Arm/Decode.lean`:
    extracts bitfields directly from a 32-bit instruction word `raw : BitVec 32`. -/
def decode_raw_inst (raw : BitVec 32) : Option ArmInst :=
  if BitVec.extractLsb' 27 3 raw == 0b111#3 &&
     BitVec.extractLsb' 24 2 raw == 0b01#2 then
    some (.LDST_Reg_imm {
      size  := BitVec.extractLsb' 30 2 raw
      V     := BitVec.extractLsb' 26 1 raw
      opc   := BitVec.extractLsb' 22 2 raw
      imm12 := BitVec.extractLsb' 10 12 raw
      Rn    := BitVec.extractLsb' 5 5 raw
      Rt    := BitVec.extractLsb' 0 5 raw
    })
  else if BitVec.extractLsb' 23 6 raw == 0b100010#6 then
    some (.DPI_Add_sub_imm {
      sf    := BitVec.extractLsb' 31 1 raw
      op    := BitVec.extractLsb' 30 1 raw
      S     := BitVec.extractLsb' 29 1 raw
      sh    := BitVec.extractLsb' 22 1 raw
      imm12 := BitVec.extractLsb' 10 12 raw
      Rn    := BitVec.extractLsb' 5 5 raw
      Rd    := BitVec.extractLsb' 0 5 raw
    })
  else if BitVec.extractLsb' 26 5 raw == 0b00101#5 then
    some (.BR_Uncond_branch_imm {
      op    := BitVec.extractLsb' 31 1 raw
      imm26 := BitVec.extractLsb' 0 26 raw
    })
  else if BitVec.extractLsb' 25 7 raw == 0b1101011#7 then
    some (.BR_Uncond_branch_reg {
      opc := BitVec.extractLsb' 21 4 raw
      op2 := BitVec.extractLsb' 16 5 raw
      op3 := BitVec.extractLsb' 10 6 raw
      Rn  := BitVec.extractLsb' 5 5 raw
      op4 := BitVec.extractLsb' 0 5 raw
    })
  else
    none

/-- Faithful transcription of LNSym's `LDST.mayModifiedRegs` (`Arm/Decode.lean:260-267`)
    and `BR.mayModifiedRegs` (`Arm/Decode.lean:103-109`).
    Note how in `Arm/Decode.lean:260`, `if getLsbD x.opc 0 then .ok []` treats
    `opc[0] = 1` (which is `LDR`!) as returning `[]`, and treats the `else` branch
    (`opc[0] = 0`, which is `STR`!) as modifying `[Rt, Rn]`. -/
def lnsym_mayModifiedRegs (inst : ArmInst) : List RegType :=
  match inst with
  | .LDST_Reg_imm x =>
    -- Exact polarity from `Arm/Decode.lean:260-267`:
    if BitVec.getLsbD x.opc 0 then [] -- Comment in LNSym says "-- Load"
    else
      if x.V = 0#1 then [.GPR x.Rt, .GPR x.Rn]
      else [.SFP x.Rt, .GPR x.Rn]
  | .DPI_Add_sub_imm x =>
    [.GPR x.Rd]
  | .BR_Uncond_branch_imm _ =>
    -- Exact return value from `Arm/Decode.lean:106-108`:
    -- "None of the branch instructions modify any GPR or SFP registers."
    []
  | .BR_Uncond_branch_reg _ =>
    []

/-- Execution semantics matching LNSym's `exec_reg_imm` (`Arm/Insts/LDST/Reg_imm.lean`),
    `exec_add_sub_imm` (`Arm/Insts/DPI/Add_sub_imm.lean`),
    `exec_uncond_branch_imm` (`Arm/Insts/BR/Uncond_branch_imm.lean`), and
    `exec_uncond_branch_reg` (`Arm/Insts/BR/Uncond_branch_reg.lean`). -/
def exec_inst (inst : ArmInst) (s : ArmState) : ArmState :=
  match inst with
  | .LDST_Reg_imm x =>
    if x.size == 0b11#2 && x.V == 0#1 && (x.opc == 0b01#2 || x.opc == 0b00#2) then
      let pc := r .PC s
      let offset : BitVec 64 := (BitVec.zeroExtend 64 x.imm12) <<< 3
      let base := r (.GPR x.Rn) s
      let addr := base + offset
      let s :=
        if x.Rn == 31#5 then
          if !(CheckSPAlignment s) then
            w .ERR (.Fault addr) s
          else if BitVec.getLsbD x.opc 0 then
            let data := read_mem_bytes 8 addr s
            write_gpr_zr x.Rt data s
          else
            let data := read_gpr_zr x.Rt s
            write_mem_bytes 8 addr data s
        else if BitVec.getLsbD x.opc 0 then
          -- LDR (unsigned offset, 64-bit)
          let data := read_mem_bytes 8 addr s
          write_gpr_zr x.Rt data s
        else
          -- STR (unsigned offset, 64-bit)
          let data := read_gpr_zr x.Rt s
          write_mem_bytes 8 addr data s
      -- Note: In LNSym's `exec_reg_imm_common` (`Arm/Insts/LDST/Reg_imm.lean:113`),
      -- `write_pc` runs unconditionally after `reg_imm_operation`, even when `Fault` is set!
      w .PC (pc + 4#64) s
    else
      w .ERR (.Unimplemented 0#32) s
  | .DPI_Add_sub_imm x =>
    if x.sf == 1#1 && x.op == 0#1 && x.S == 0#1 && x.sh == 0#1 then
      let pc := r .PC s
      let op1 := r (.GPR x.Rn) s
      let op2 := BitVec.zeroExtend 64 x.imm12
      let s := w (.GPR x.Rd) (op1 + op2) s
      w .PC (pc + 4#64) s
    else
      w .ERR (.Unimplemented 0#32) s
  | .BR_Uncond_branch_imm x =>
    let orig_pc := r .PC s
    let offset := BitVec.signExtend 64 (x.imm26 ++ 0b00#2)
    let s := if x.op == 1#1 then w (.GPR 30#5) (orig_pc + 4#64) s else s
    w .PC (orig_pc + offset) s
  | .BR_Uncond_branch_reg x =>
    if x.opc == 0b0010#4 && x.op2 == 0b11111#5 && x.op3 == 0b000000#6 && x.op4 == 0b00000#5 then
      let target := read_gpr_zr x.Rn s
      w .PC target s
    else
      w .ERR (.Unimplemented 0#32) s

def stepi (s : ArmState) : ArmState :=
  match r .ERR s with
  | .None =>
    let pc := r .PC s
    match fetch_inst pc s with
    | none => w .ERR (.NotFound pc) s
    | some raw =>
      match decode_raw_inst raw with
      | none => w .ERR (.Unimplemented raw) s
      | some inst => exec_inst inst s
  | _ => s

def run (n : Nat) (s : ArmState) : ArmState :=
  match n with
  | 0 => s
  | n' + 1 => run n' (stepi s)

theorem stepi_error_stutter (s : ArmState) (herr : r .ERR s ≠ .None) :
    stepi s = s := by
  unfold stepi
  cases h : r .ERR s <;> simp_all

theorem exec_inst_preserves_program (inst : ArmInst) (s : ArmState) :
    (exec_inst inst s).program = s.program := by
  cases inst with
  | LDST_Reg_imm x =>
    unfold exec_inst
    dsimp only
    split <;> try rfl
    simp only [w_program]
    split
    · split <;> try rfl
      split
      · unfold write_gpr_zr; split <;> rfl
      · rfl
    · split
      · unfold write_gpr_zr; split <;> rfl
      · rfl
  | DPI_Add_sub_imm x =>
    unfold exec_inst; dsimp only; split <;> rfl
  | BR_Uncond_branch_imm x =>
    unfold exec_inst; dsimp only; simp only [w_program]; split <;> rfl
  | BR_Uncond_branch_reg x =>
    unfold exec_inst; dsimp only; split <;> rfl

theorem stepi_preserves_program (s : ArmState) :
    (stepi s).program = s.program := by
  unfold stepi
  dsimp only
  split <;> try rfl
  split <;> try rfl
  split <;> first | rfl | exact exec_inst_preserves_program _ _

/-! ### Concrete Proofs of LNSym's Two `mayModifiedRegs` Bugs (`Arm/Decode.lean`) -/

/-- `ldr x2, [x0]` (`0xf9400002#32`): `opc = 0b01`, so `opc[0] = true`. -/
def ldr_x2_x0_word : BitVec 32 := 0xf9400002#32

/-- `str x1, [x0]` (`0xf9000001#32`): `opc = 0b00`, so `opc[0] = false`. -/
def str_x1_x0_word : BitVec 32 := 0xf9000001#32

/-- `bl #4` (`0x94000001#32`): `op = 1`, `imm26 = 1`. -/
def bl_4_word : BitVec 32 := 0x94000001#32

/-- Bug 1a (`Arm/Decode.lean:260-267`): `ldr x2, [x0]` decodes to `.LDST_Reg_imm` with
    `opc = 0b01#2` (`getLsbD opc 0 = true`), so `lnsym_mayModifiedRegs` returns `[]`,
    even though `exec_inst` overwrites `.GPR 2#5` with `read_mem_bytes 8 (r (.GPR 0#5) s) s`! -/
theorem bug1a_ldst_mayModifiedRegs_omits_ldr_destination (s : ArmState) :
    ∃ inst,
      decode_raw_inst ldr_x2_x0_word = some inst ∧
      lnsym_mayModifiedRegs inst = [] ∧
      r (.GPR 2#5) (exec_inst inst s) = read_mem_bytes 8 (r (.GPR 0#5) s) s := by
  refine ⟨.LDST_Reg_imm ⟨0b11#2, 0#1, 0b01#2, 0#12, 0#5, 2#5⟩, ?_, ?_, ?_⟩
  · decide
  · decide
  · simp [exec_inst, write_gpr_zr]

/-- Bug 1b (`Arm/Decode.lean:260-267`): `str x1, [x0]` decodes to `.LDST_Reg_imm` with
    `opc = 0b00#2` (`getLsbD opc 0 = false`), so `lnsym_mayModifiedRegs` reports
    `[.GPR 1#5, .GPR 0#5]` as modified, even though `exec_inst` modifies NO general-purpose
    registers! -/
theorem bug1b_ldst_mayModifiedRegs_falsely_reports_str_registers (s : ArmState) (reg : BitVec 5) :
    ∃ inst,
      decode_raw_inst str_x1_x0_word = some inst ∧
      lnsym_mayModifiedRegs inst = [.GPR 1#5, .GPR 0#5] ∧
      r (.GPR reg) (exec_inst inst s) = r (.GPR reg) s := by
  refine ⟨.LDST_Reg_imm ⟨0b11#2, 0#1, 0b00#2, 0#12, 0#5, 1#5⟩, ?_, ?_, ?_⟩
  · decide
  · decide
  · simp [exec_inst]

/-- Bug 2 (`Arm/Decode.lean:103-109`): `bl #4` (`0x94000001#32`) decodes to
    `.BR_Uncond_branch_imm ⟨1#1, 1#26⟩`, and `lnsym_mayModifiedRegs` returns `[]`,
    even though `exec_inst` writes `r .PC s + 4#64` to `.GPR 30#5` (`LR`)! -/
theorem bug2_br_mayModifiedRegs_omits_bl_link_register (s : ArmState) :
    ∃ inst,
      decode_raw_inst bl_4_word = some inst ∧
      lnsym_mayModifiedRegs inst = [] ∧
      r (.GPR 30#5) (exec_inst inst s) = r .PC s + 4#64 := by
  refine ⟨.BR_Uncond_branch_imm ⟨1#1, 1#26⟩, ?_, ?_, ?_⟩
  · decide
  · decide
  · simp [exec_inst]

/-- Anomaly 3 (`Arm/Insts/LDST/Reg_imm.lean:109-113`): When `Rn = 31#5` (`SP`) and
    `CheckSPAlignment s = false`, `exec_inst` sets `r .ERR = .Fault addr` AND STILL
    advances `r .PC` by `4#64`. -/
theorem anomaly3_ldst_reg_imm_fault_still_advances_pc (s : ArmState)
    (hunaligned : CheckSPAlignment s = false) :
    let inst := ArmInst.LDST_Reg_imm ⟨0b11#2, 0#1, 0b01#2, 0#12, 31#5, 2#5⟩
    r .ERR (exec_inst inst s) = .Fault (r (.GPR 31#5) s) ∧
    r .PC (exec_inst inst s) = r .PC s + 4#64 := by
  simp [exec_inst, hunaligned]

/-! ## Section 5: Negative Control — Unaugmented `ArmState` Misses Unauthorized Reads & Self-Stores -/

/-- Instruction words used in our three comparative leaf programs:
    - `0xf9400002#32` : `ldr x2, [x0]`       (`imm12 = 0`)
    - `0xf9400402#32` : `ldr x2, [x0, #8]`   (`imm12 = 1`, scaled by 8 -> `+8`)
    - `0xf9000001#32` : `str x1, [x0]`       (`imm12 = 0`)
    - `0xf9000402#32` : `str x2, [x0, #8]`   (`imm12 = 1`, scaled by 8 -> `+8`)
    - `0x91000040#32` : `add x0, x2, #0`     (`mov x0, x2`)
    - `0xd65f03c0#32` : `ret` (`x30`) -/
def ldr_x2_x0_plus_8_word : BitVec 32 := 0xf9400402#32
def str_x2_x0_plus_8_word : BitVec 32 := 0xf9000402#32
def add_x0_x2_0_word      : BitVec 32 := 0x91000040#32
def ret_word              : BitVec 32 := 0xd65f03c0#32

/-- Program 1: Valid 64-bit swap leaf (`mem::replace(&mut *x0, x1)`). -/
def prog_valid_swap : Program :=
  [ (0x1000#64, ldr_x2_x0_word),
    (0x1004#64, str_x1_x0_word),
    (0x1008#64, add_x0_x2_0_word),
    (0x100c#64, ret_word) ]

/-- Program 2: Performs an unauthorized out-of-bounds read `ldr x2, [x0, #8]`
    before overwriting `x2` with `ldr x2, [x0]`. -/
def prog_dead_oob_load : Program :=
  [ (0x1000#64, ldr_x2_x0_plus_8_word),
    (0x1004#64, ldr_x2_x0_word),
    (0x1008#64, str_x1_x0_word),
    (0x100c#64, add_x0_x2_0_word),
    (0x1010#64, ret_word) ]

/-- Program 3: Reads `[x0, #8]` into `x2` and writes `x2` back to `[x0, #8]`
    (an unauthorized store to `[x0 + 8, x0 + 16)`!) before executing the swap on `[x0]`. -/
def prog_redundant_oob_store : Program :=
  [ (0x1000#64, ldr_x2_x0_plus_8_word),
    (0x1004#64, str_x2_x0_plus_8_word),
    (0x1008#64, ldr_x2_x0_word),
    (0x100c#64, str_x1_x0_word),
    (0x1010#64, add_x0_x2_0_word),
    (0x1014#64, ret_word) ]

/-- Embed a `Program` into an initial `ArmState` at `pc = 0x1000#64` with `error = .None`. -/
def withProgram (s : ArmState) (p : Program) : ArmState :=
  { s with pc := 0x1000#64, program := p, error := .None }

/-- Canonical post-state of the 64-bit swap leaf (`mem::replace(&mut *x0, x1)`)
    parameterized only by the program field `p`. -/
def expectedSwapState (s : ArmState) (p : Program) : ArmState :=
  let v0 := Memory.read_bytes 8 (s.gpr 0#5) s.mem
  let m1 := Memory.write_bytes 8 (s.gpr 0#5) (s.gpr 1#5) s.mem
  { gpr     := write (write s.gpr 2#5 v0) 0#5 v0
    sfp     := s.sfp
    pc      := s.gpr 30#5
    pstate  := s.pstate
    mem     := m1
    program := p
    error   := .None }

@[simp]
theorem write_gpr_shadow (r_idx : BitVec 5) (v₁ v₂ : BitVec 64)
    (g : Store (BitVec 5) (BitVec 64)) :
    write (write g r_idx v₁) r_idx v₂ = write g r_idx v₂ := by
  funext r
  simp only [write]
  split <;> rfl

theorem run_prog_valid_swap_eq (s : ArmState) :
    run 4 (withProgram s prog_valid_swap) = expectedSwapState s prog_valid_swap := by
  simp [run, stepi, withProgram, expectedSwapState, r, w, write, fetch_inst,
    Program.find?, prog_valid_swap, ldr_x2_x0_word, str_x1_x0_word,
    add_x0_x2_0_word, ret_word, decode_raw_inst, exec_inst,
    write_gpr_zr, read_gpr_zr, read_mem_bytes, write_mem_bytes]

theorem run_prog_dead_oob_load_eq (s : ArmState) :
    run 5 (withProgram s prog_dead_oob_load) = expectedSwapState s prog_dead_oob_load := by
  simp [run, stepi, withProgram, expectedSwapState, r, w, write, fetch_inst,
    Program.find?, prog_dead_oob_load, ldr_x2_x0_plus_8_word, ldr_x2_x0_word,
    str_x1_x0_word, add_x0_x2_0_word, ret_word, decode_raw_inst, exec_inst,
    write_gpr_zr, read_gpr_zr, read_mem_bytes, write_mem_bytes]

theorem run_prog_redundant_oob_store_eq (s : ArmState) :
    run 6 (withProgram s prog_redundant_oob_store) = expectedSwapState s prog_redundant_oob_store := by
  simp [run, stepi, withProgram, expectedSwapState, r, w, write, fetch_inst,
    Program.find?, prog_redundant_oob_store, ldr_x2_x0_plus_8_word, str_x2_x0_plus_8_word,
    ldr_x2_x0_word, str_x1_x0_word, add_x0_x2_0_word, ret_word, decode_raw_inst, exec_inst,
    write_gpr_zr, read_gpr_zr, read_mem_bytes, write_mem_bytes,
    Memory.write_bytes_read_bytes_eq]

/-- Negative-Control Theorem:
    For ANY initial `ArmState` `s`, running `prog_valid_swap` (4 steps),
    `prog_dead_oob_load` (5 steps), and `prog_redundant_oob_store` (6 steps)
    produces the EXACT same final `gpr`, `sfp`, `pc`, `pstate`, `mem` (extensionally equal
    over all `2^64` addresses!), and `error = .None`!
    Because LNSym's `ArmState` has a total `mem : BitVec 64 → BitVec 8` and records no
    memory-access trace, pure initial-to-final `ArmState` theorems cannot distinguish
    a valid swap leaf from one that reads or overwrites unauthorized memory! -/
theorem lnsym_unaugmented_state_blind_to_dead_load_and_self_store (s : ArmState) :
    let s_valid := run 4 (withProgram s prog_valid_swap)
    let s_dead_load := run 5 (withProgram s prog_dead_oob_load)
    let s_self_store := run 6 (withProgram s prog_redundant_oob_store)
    s_dead_load.gpr = s_valid.gpr ∧
    s_dead_load.sfp = s_valid.sfp ∧
    s_dead_load.pc = s_valid.pc ∧
    s_dead_load.pstate = s_valid.pstate ∧
    s_dead_load.mem = s_valid.mem ∧
    s_dead_load.error = .None ∧
    s_self_store.gpr = s_valid.gpr ∧
    s_self_store.sfp = s_valid.sfp ∧
    s_self_store.pc = s_valid.pc ∧
    s_self_store.pstate = s_valid.pstate ∧
    s_self_store.mem = s_valid.mem ∧
    s_self_store.error = .None := by
  dsimp only
  rw [run_prog_valid_swap_eq, run_prog_dead_oob_load_eq, run_prog_redundant_oob_store_eq]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 6: Positive Bridge — Footprint-Augmented LNSym Wrapper into Anneal's `SmallStepMachine` -/

inductive AccessKind where
  | read
  | write
  deriving DecidableEq, Repr

structure MemAccess where
  kind    : AccessKind
  addr    : BitVec 64
  size    : Nat
  aligned : Bool
  deriving DecidableEq, Repr

/-- Extract the memory accesses performed by a single decoded LNSym instruction in state `s`,
    including natural size alignment (`addr.toNat % 8 == 0` for 64-bit `LDR`/`STR`). -/
def instMemAccesses (inst : ArmInst) (s : ArmState) : List MemAccess :=
  match inst with
  | .LDST_Reg_imm x =>
    if x.size == 0b11#2 && x.V == 0#1 && (x.opc == 0b01#2 || x.opc == 0b00#2) then
      let offset : BitVec 64 := (BitVec.zeroExtend 64 x.imm12) <<< 3
      let addr := r (.GPR x.Rn) s + offset
      let aligned := (addr.toNat % 8 == 0) &&
        (if x.Rn == 31#5 then CheckSPAlignment s else true)
      let kind := if BitVec.getLsbD x.opc 0 then AccessKind.read else AccessKind.write
      [{ kind := kind, addr := addr, size := 8, aligned := aligned }]
    else
      []
  | _ => []

/-- An Anneal memory-footprint policy parameterized over LNSym's `mem_subset'` predicate. -/
structure FootprintPolicy where
  allowRead  : BitVec 64 → Nat → Prop
  allowWrite : BitVec 64 → Nat → Prop
  [decRead   : ∀ a n, Decidable (allowRead a n)]
  [decWrite  : ∀ a n, Decidable (allowWrite a n)]

attribute [instance] FootprintPolicy.decRead FootprintPolicy.decWrite

def checkAccess (policy : FootprintPolicy) (acc : MemAccess) : Bool :=
  acc.aligned &&
  match acc.kind with
  | .read  => decide (policy.allowRead acc.addr acc.size)
  | .write => decide (policy.allowWrite acc.addr acc.size)

/-- Observable outcome at function return (`PC = retPC`): return value in `x0` and final memory. -/
structure SwapObs where
  ret_x0 : BitVec 64
  mem    : Memory

/-- Footprint-augmented small-step machine wrapping LNSym's `stepi` / `exec_inst`:
    - Halts with `SwapObs` when `r .PC s = retPC` and `r .ERR s = .None`.
    - Fails with `.failed .ub` if `r .ERR s ≠ .None`, fetch/decode fails, `exec_inst`
      sets `r .ERR ≠ .None`, or any memory access in `instMemAccesses` violates `policy`. -/
def footprintLNSymMachine (policy : FootprintPolicy) (retPC : BitVec 64) :
    SmallStepMachine ArmState SwapObs where
  step s :=
    match r .ERR s with
    | .None =>
      let pc := r .PC s
      if pc == retPC then
        .halted { ret_x0 := r (.GPR 0#5) s, mem := s.mem }
      else
        match fetch_inst pc s with
        | none => .failed .ub
        | some raw =>
          match decode_raw_inst raw with
          | none => .failed .ub
          | some inst =>
            if (instMemAccesses inst s).all (checkAccess policy) then
              let s' := exec_inst inst s
              match r .ERR s' with
              | .None => .stepped s'
              | _ => .failed .ub
            else
              .failed .ub
    | _ => .failed .ub

/-- Policy authorizing reads and writes ONLY within `[base, base + 8)`. -/
def singleSlotPolicy (base : BitVec 64) : FootprintPolicy where
  allowRead  a n := a = base ∧ n = 8 ∧ mem_legal' base 8
  allowWrite a n := a = base ∧ n = 8 ∧ mem_legal' base 8
  decRead    _ _ := inferInstance
  decWrite   _ _ := inferInstance

/-- Policy authorizing reads within `[base, base + 16)` (e.g., two 8-byte slots)
    but writes ONLY within `[base, base + 8)` (the second slot is `readonly`). -/
def readTwoWriteOnePolicy (base : BitVec 64) : FootprintPolicy where
  allowRead  a n := (a = base ∨ a = base + 8#64) ∧ n = 8
  allowWrite a n := a = base ∧ n = 8
  decRead    _ _ := inferInstance
  decWrite   _ _ := inferInstance

/-- Abstract source specification for 64-bit `core::mem::replace(&mut *base, new_val)`. -/
structure SwapInput where
  base    : BitVec 64
  new_val : BitVec 64
  ret_pc  : BitVec 64
  sp      : BitVec 64
  mem     : Memory

def ValidSwapInput (inp : SwapInput) : Prop :=
  mem_legal' inp.base 8 ∧
  inp.base.toNat % 8 = 0 ∧
  inp.ret_pc ≠ 0x1000#64 ∧
  inp.ret_pc ≠ 0x1004#64 ∧
  inp.ret_pc ≠ 0x1008#64 ∧
  inp.ret_pc ≠ 0x100c#64

def initSwapArmState (inp : SwapInput) (prog : Program) : ArmState where
  gpr     := fun r =>
    if r = 0#5 then inp.base
    else if r = 1#5 then inp.new_val
    else if r = 30#5 then inp.ret_pc
    else if r = 31#5 then inp.sp
    else 0#64
  sfp     := fun _ => 0#128
  pc      := 0x1000#64
  pstate  := ⟨0#1, 0#1, 0#1, 0#1⟩
  mem     := inp.mem
  program := prog
  error   := .None

/-- Positive Theorem 1: Under `singleSlotPolicy inp.base`, `prog_valid_swap` steps
    cleanly through all 4 instructions and halts at `inp.ret_pc` with:
    - `ret_x0 = Memory.read_bytes 8 inp.base inp.mem` (the old 64-bit value at `base`),
    - `Memory.read_bytes 8 inp.base obs.mem = inp.new_val` (the new 64-bit value stored at `base`),
    - `Memory.read_bytes n other obs.mem = Memory.read_bytes n other inp.mem` for every
      region `(other, n)` disjoint from `(inp.base, 8)` (`mem_separate'`). -/
theorem footprint_machine_valid_swap_halts (inp : SwapInput) (hvalid : ValidSwapInput inp) :
    let M := footprintLNSymMachine (singleSlotPolicy inp.base) inp.ret_pc
    let s₀ := initSwapArmState inp prog_valid_swap
    let expectedObs : SwapObs := {
      ret_x0 := Memory.read_bytes 8 inp.base inp.mem
      mem    := Memory.write_bytes 8 inp.base inp.new_val inp.mem
    }
    ReachesPrefix M 4 s₀ (.halted expectedObs) ∧
    Memory.read_bytes 8 inp.base expectedObs.mem = inp.new_val ∧
    (∀ other n, mem_separate' other n inp.base 8 →
      Memory.read_bytes n other expectedObs.mem = Memory.read_bytes n other inp.mem) := by
  obtain ⟨hlegal, halign, hpc0, hpc4, hpc8, hpcc⟩ := hvalid
  dsimp only
  refine ⟨?_, Memory.read_bytes_write_bytes_same 8 inp.base inp.new_val inp.mem hlegal,
    fun other n hsep => Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' n 8 other inp.base inp.new_val inp.mem hsep⟩
  have h0 : 0x1000#64 ≠ inp.ret_pc := Ne.symm hpc0
  have h4 : 0x1004#64 ≠ inp.ret_pc := Ne.symm hpc4
  have h8 : 0x1008#64 ≠ inp.ret_pc := Ne.symm hpc8
  have hc : 0x100c#64 ≠ inp.ret_pc := Ne.symm hpcc
  apply ReachesPrefix.succ (s' := exec_inst (.LDST_Reg_imm ⟨0b11#2, 0#1, 0b01#2, 0#12, 0#5, 2#5⟩)
    (initSwapArmState inp prog_valid_swap))
  · simp [footprintLNSymMachine, initSwapArmState, r, w, h0, fetch_inst, prog_valid_swap,
      Program.find?, ldr_x2_x0_word, decode_raw_inst, instMemAccesses,
      checkAccess, singleSlotPolicy, halign, hlegal, exec_inst, write_gpr_zr]
  apply ReachesPrefix.succ (s' := exec_inst (.LDST_Reg_imm ⟨0b11#2, 0#1, 0b00#2, 0#12, 0#5, 1#5⟩)
    (exec_inst (.LDST_Reg_imm ⟨0b11#2, 0#1, 0b01#2, 0#12, 0#5, 2#5⟩)
      (initSwapArmState inp prog_valid_swap)))
  · simp [footprintLNSymMachine, initSwapArmState, r, w, write, h4, fetch_inst, prog_valid_swap,
      Program.find?, str_x1_x0_word, decode_raw_inst, instMemAccesses,
      checkAccess, singleSlotPolicy, halign, hlegal, exec_inst, write_gpr_zr, write_mem_bytes]
  apply ReachesPrefix.succ (s' := exec_inst (.DPI_Add_sub_imm ⟨1#1, 0#1, 0#1, 0#1, 0#12, 2#5, 0#5⟩)
    (exec_inst (.LDST_Reg_imm ⟨0b11#2, 0#1, 0b00#2, 0#12, 0#5, 1#5⟩)
      (exec_inst (.LDST_Reg_imm ⟨0b11#2, 0#1, 0b01#2, 0#12, 0#5, 2#5⟩)
        (initSwapArmState inp prog_valid_swap))))
  · simp [footprintLNSymMachine, initSwapArmState, r, w, write, h8, fetch_inst, prog_valid_swap,
      Program.find?, add_x0_x2_0_word, decode_raw_inst, instMemAccesses,
      exec_inst, write_gpr_zr, write_mem_bytes]
  apply ReachesPrefix.succ (s' := exec_inst (.BR_Uncond_branch_reg ⟨0b0010#4, 0b11111#5, 0#6, 30#5, 0#5⟩)
    (exec_inst (.DPI_Add_sub_imm ⟨1#1, 0#1, 0#1, 0#1, 0#12, 2#5, 0#5⟩)
      (exec_inst (.LDST_Reg_imm ⟨0b11#2, 0#1, 0b00#2, 0#12, 0#5, 1#5⟩)
        (exec_inst (.LDST_Reg_imm ⟨0b11#2, 0#1, 0b01#2, 0#12, 0#5, 2#5⟩)
          (initSwapArmState inp prog_valid_swap)))))
  · simp [footprintLNSymMachine, initSwapArmState, r, w, write, hc, fetch_inst, prog_valid_swap,
      Program.find?, ret_word, decode_raw_inst, instMemAccesses,
      exec_inst, write_gpr_zr, write_mem_bytes, read_gpr_zr]
  have hstep4 :
      (footprintLNSymMachine (singleSlotPolicy inp.base) inp.ret_pc).step
        (exec_inst (.BR_Uncond_branch_reg ⟨0b0010#4, 0b11111#5, 0#6, 30#5, 0#5⟩)
          (exec_inst (.DPI_Add_sub_imm ⟨1#1, 0#1, 0#1, 0#1, 0#12, 2#5, 0#5⟩)
            (exec_inst (.LDST_Reg_imm ⟨0b11#2, 0#1, 0b00#2, 0#12, 0#5, 1#5⟩)
               (exec_inst (.LDST_Reg_imm ⟨0b11#2, 0#1, 0b01#2, 0#12, 0#5, 2#5⟩)
                 (initSwapArmState inp prog_valid_swap))))) =
      .halted {
        ret_x0 := Memory.read_bytes 8 inp.base inp.mem
        mem    := Memory.write_bytes 8 inp.base inp.new_val inp.mem
      } := by
    simp [footprintLNSymMachine, initSwapArmState, r, w, write, exec_inst,
      write_gpr_zr, write_mem_bytes, read_gpr_zr, read_mem_bytes]
  rw [← hstep4]
  exact ReachesPrefix.zero _

/-- Positive Theorem 2: The footprint-augmented LNSym machine catches the dead
    out-of-bounds load in `prog_dead_oob_load` on step 0 (`ReachesPrefix M 0 s₀ (.failed .ub)`),
    even though `prog_dead_oob_load` produces the exact same final `ArmState` as `prog_valid_swap`! -/
theorem footprint_machine_rejects_dead_oob_load (inp : SwapInput) (hvalid : ValidSwapInput inp) :
    let M := footprintLNSymMachine (singleSlotPolicy inp.base) inp.ret_pc
    let s₀ := initSwapArmState inp prog_dead_oob_load
    ReachesPrefix M 0 s₀ (.failed .ub) ∧
    ¬ (BehaviorOf M s₀).defined := by
  obtain ⟨_, _, hpc0, _, _, _⟩ := hvalid
  dsimp only
  have h0 : 0x1000#64 ≠ inp.ret_pc := Ne.symm hpc0
  have hne : inp.base + 8#64 ≠ inp.base := by
    intro heq
    have hsub : inp.base + 8#64 - inp.base = inp.base - inp.base := congrArg (· - inp.base) heq
    rw [BitVec.add_comm inp.base 8#64, BitVec.add_sub_cancel, BitVec.sub_self] at hsub
    exact absurd hsub (by decide)
  have hstep0 :
      (footprintLNSymMachine (singleSlotPolicy inp.base) inp.ret_pc).step
        (initSwapArmState inp prog_dead_oob_load) = .failed .ub := by
    simp [footprintLNSymMachine, initSwapArmState, r, h0, fetch_inst, prog_dead_oob_load,
      Program.find?, ldr_x2_x0_plus_8_word, decode_raw_inst, instMemAccesses,
      checkAccess, singleSlotPolicy, hne]
  refine ⟨?_, ?_⟩
  · rw [← hstep0]
    exact ReachesPrefix.zero _
  · intro hdef
    apply hdef 0
    rw [← hstep0]
    exact ReachesPrefix.zero _

/-- Positive Theorem 3: Under `readTwoWriteOnePolicy inp.base` (which allows reading both
    `[base, base+8)` and `[base+8, base+16)` but allows writing ONLY `[base, base+8)`),
    `prog_redundant_oob_store` steps past `ldr x2, [x0, #8]` at step 0 and is caught at step 1
    when executing the self-store `str x2, [x0, #8]`, transitioning to `.failed .ub`! -/
theorem footprint_machine_rejects_redundant_oob_store (inp : SwapInput)
    (hvalid : ValidSwapInput inp) :
    let M := footprintLNSymMachine (readTwoWriteOnePolicy inp.base) inp.ret_pc
    let s₀ := initSwapArmState inp prog_redundant_oob_store
    ReachesPrefix M 1 s₀ (.failed .ub) ∧
    ¬ (BehaviorOf M s₀).defined := by
  obtain ⟨_, halign, hpc0, hpc4, _, _⟩ := hvalid
  dsimp only
  have h0 : 0x1000#64 ≠ inp.ret_pc := Ne.symm hpc0
  have h4 : 0x1004#64 ≠ inp.ret_pc := Ne.symm hpc4
  have hne : inp.base + 8#64 ≠ inp.base := by
    intro heq
    have hsub : inp.base + 8#64 - inp.base = inp.base - inp.base := congrArg (· - inp.base) heq
    rw [BitVec.add_comm inp.base 8#64, BitVec.add_sub_cancel, BitVec.sub_self] at hsub
    exact absurd hsub (by decide)
  have hreach1 :
      ReachesPrefix (footprintLNSymMachine (readTwoWriteOnePolicy inp.base) inp.ret_pc) 1
        (initSwapArmState inp prog_redundant_oob_store) (.failed .ub) := by
    apply ReachesPrefix.succ (s' := exec_inst (.LDST_Reg_imm ⟨0b11#2, 0#1, 0b01#2, 1#12, 0#5, 2#5⟩)
      (initSwapArmState inp prog_redundant_oob_store))
    · simp [footprintLNSymMachine, initSwapArmState, r, w, h0, fetch_inst, prog_redundant_oob_store,
        Program.find?, ldr_x2_x0_plus_8_word, decode_raw_inst, instMemAccesses,
        checkAccess, readTwoWriteOnePolicy, halign, exec_inst, write_gpr_zr]
    · have hstep1 :
          (footprintLNSymMachine (readTwoWriteOnePolicy inp.base) inp.ret_pc).step
            (exec_inst (.LDST_Reg_imm ⟨0b11#2, 0#1, 0b01#2, 1#12, 0#5, 2#5⟩)
              (initSwapArmState inp prog_redundant_oob_store)) = .failed .ub := by
        simp [footprintLNSymMachine, initSwapArmState, r, w, write, h4, fetch_inst,
          prog_redundant_oob_store, Program.find?, str_x2_x0_plus_8_word, decode_raw_inst,
          instMemAccesses, checkAccess, readTwoWriteOnePolicy, hne, exec_inst, write_gpr_zr]
      rw [← hstep1]
      exact ReachesPrefix.zero _
  exact ⟨hreach1, fun hdef => hdef 1 hreach1⟩

/-! ### End-to-End Anneal `Language` and `Compiles` Instantiation -/

def SwapSrcLanguage : Language where
  Prog  := Unit
  Query := SwapInput
  Out   := SwapObs
  sem   := fun _ inp => {
    defined := ValidSwapInput inp
    val     := fun _ obs =>
      obs.ret_x0 = Memory.read_bytes 8 inp.base inp.mem ∧
      Memory.read_bytes 8 inp.base obs.mem = inp.new_val ∧
      (∀ other n, mem_separate' other n inp.base 8 →
        Memory.read_bytes n other obs.mem = Memory.read_bytes n other inp.mem)
  }

def SwapTgtLanguage : Language where
  Prog  := Program
  Query := SwapInput
  Out   := SwapObs
  sem   := fun prog inp =>
    BehaviorOf
      (footprintLNSymMachine (singleSlotPolicy inp.base) inp.ret_pc)
      (initSwapArmState inp prog)

theorem valid_swap_no_ub_at_any_step (inp : SwapInput) (hvalid : ValidSwapInput inp) :
    ∀ n, ¬ ReachesPrefix
      (footprintLNSymMachine (singleSlotPolicy inp.base) inp.ret_pc)
      n (initSwapArmState inp prog_valid_swap) (.failed .ub) := by
  have ⟨hreach4, _, _⟩ := footprint_machine_valid_swap_halts inp hvalid
  have ⟨hreach4_copy, _, _⟩ := footprint_machine_valid_swap_halts inp hvalid
  rcases hreach4 with _ | ⟨hstep0, _ | ⟨hstep1, _ | ⟨hstep2, _ | ⟨hstep3, hzero4⟩⟩⟩⟩
  have hr0 : ReachesPrefix (footprintLNSymMachine (singleSlotPolicy inp.base) inp.ret_pc) 0
      (initSwapArmState inp prog_valid_swap) _ :=
    hstep0 ▸ ReachesPrefix.zero _
  have hr1 : ReachesPrefix (footprintLNSymMachine (singleSlotPolicy inp.base) inp.ret_pc) 1
      (initSwapArmState inp prog_valid_swap) _ :=
    ReachesPrefix.succ hstep0 (hstep1 ▸ ReachesPrefix.zero _)
  have hr2 : ReachesPrefix (footprintLNSymMachine (singleSlotPolicy inp.base) inp.ret_pc) 2
      (initSwapArmState inp prog_valid_swap) _ :=
    ReachesPrefix.succ hstep0 (ReachesPrefix.succ hstep1 (hstep2 ▸ ReachesPrefix.zero _))
  have hr3 : ReachesPrefix (footprintLNSymMachine (singleSlotPolicy inp.base) inp.ret_pc) 3
      (initSwapArmState inp prog_valid_swap) _ :=
    ReachesPrefix.succ hstep0 (ReachesPrefix.succ hstep1
      (ReachesPrefix.succ hstep2 (hstep3 ▸ ReachesPrefix.zero _)))
  intro n hfail
  by_cases hn4 : 4 ≤ n
  · have ⟨_, hreq⟩ := ReachesPrefix.TerminalNoStepFurther hreach4_copy (by simp) hfail hn4
    nomatch hreq
  · have hlt : n < 4 := by omega
    rcases n with _ | _ | _ | _ | n
    · have hdet := ReachesPrefix.deterministic hfail hr0; nomatch hdet
    · have hdet := ReachesPrefix.deterministic hfail hr1; nomatch hdet
    · have hdet := ReachesPrefix.deterministic hfail hr2; nomatch hdet
    · have hdet := ReachesPrefix.deterministic hfail hr3; nomatch hdet
    · omega

theorem swap_tgt_well_formed :
    SwapTgtLanguage.sem prog_valid_swap ≤ SwapTgtLanguage.WellFormedOn ValidSwapInput := by
  intro inp hvalid
  exact ⟨valid_swap_no_ub_at_any_step inp hvalid, fun _ _ => True.intro⟩

theorem swap_compiles :
    Compiles SwapSrcLanguage SwapTgtLanguage id () prog_valid_swap := by
  intro inp hvalid
  refine ⟨valid_swap_no_ub_at_any_step inp hvalid, ?_⟩
  intro obs ⟨n, hreach⟩
  have ⟨hreach4, hnew, hframe⟩ := footprint_machine_valid_swap_halts inp hvalid
  have ⟨hreach4_copy, _, _⟩ := footprint_machine_valid_swap_halts inp hvalid
  rcases hreach4 with _ | ⟨hstep0, _ | ⟨hstep1, _ | ⟨hstep2, _ | ⟨hstep3, _⟩⟩⟩⟩
  have hr0 : ReachesPrefix (footprintLNSymMachine (singleSlotPolicy inp.base) inp.ret_pc) 0
      (initSwapArmState inp prog_valid_swap) _ :=
    hstep0 ▸ ReachesPrefix.zero _
  have hr1 : ReachesPrefix (footprintLNSymMachine (singleSlotPolicy inp.base) inp.ret_pc) 1
      (initSwapArmState inp prog_valid_swap) _ :=
    ReachesPrefix.succ hstep0 (hstep1 ▸ ReachesPrefix.zero _)
  have hr2 : ReachesPrefix (footprintLNSymMachine (singleSlotPolicy inp.base) inp.ret_pc) 2
      (initSwapArmState inp prog_valid_swap) _ :=
    ReachesPrefix.succ hstep0 (ReachesPrefix.succ hstep1 (hstep2 ▸ ReachesPrefix.zero _))
  have hr3 : ReachesPrefix (footprintLNSymMachine (singleSlotPolicy inp.base) inp.ret_pc) 3
      (initSwapArmState inp prog_valid_swap) _ :=
    ReachesPrefix.succ hstep0 (ReachesPrefix.succ hstep1
      (ReachesPrefix.succ hstep2 (hstep3 ▸ ReachesPrefix.zero _)))
  by_cases hn4 : 4 ≤ n
  · have ⟨_, hreq⟩ := ReachesPrefix.TerminalNoStepFurther hreach4_copy (by simp) hreach hn4
    injection hreq with hobs
    subst hobs
    exact ⟨rfl, hnew, hframe⟩
  · have hlt : n < 4 := by omega
    rcases n with _ | _ | _ | _ | n
    · have hdet := ReachesPrefix.deterministic hreach hr0; nomatch hdet
    · have hdet := ReachesPrefix.deterministic hreach hr1; nomatch hdet
    · have hdet := ReachesPrefix.deterministic hreach hr2; nomatch hdet
    · have hdet := ReachesPrefix.deterministic hreach hr3; nomatch hdet
    · omega

/-! ## Section 7: Axiom Audit -/

/--
info: 'LNSymArchitectureAndBridgeProbe.Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate'' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate'

/-- info: 'LNSymArchitectureAndBridgeProbe.Memory.write_bytes_read_bytes_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Memory.write_bytes_read_bytes_eq

/--
info: 'LNSymArchitectureAndBridgeProbe.bug1a_ldst_mayModifiedRegs_omits_ldr_destination' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms bug1a_ldst_mayModifiedRegs_omits_ldr_destination

/--
info: 'LNSymArchitectureAndBridgeProbe.bug1b_ldst_mayModifiedRegs_falsely_reports_str_registers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms bug1b_ldst_mayModifiedRegs_falsely_reports_str_registers

/--
info: 'LNSymArchitectureAndBridgeProbe.bug2_br_mayModifiedRegs_omits_bl_link_register' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms bug2_br_mayModifiedRegs_omits_bl_link_register

/--
info: 'LNSymArchitectureAndBridgeProbe.lnsym_unaugmented_state_blind_to_dead_load_and_self_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms lnsym_unaugmented_state_blind_to_dead_load_and_self_store

/-- info: 'LNSymArchitectureAndBridgeProbe.footprint_machine_rejects_dead_oob_load' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms footprint_machine_rejects_dead_oob_load

/--
info: 'LNSymArchitectureAndBridgeProbe.footprint_machine_rejects_redundant_oob_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms footprint_machine_rejects_redundant_oob_store

/-- info: 'LNSymArchitectureAndBridgeProbe.swap_compiles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms swap_compiles

end LNSymArchitectureAndBridgeProbe
