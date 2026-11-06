/-
  Standalone Lean 4.34.1 mechanization for:
  `cslib-bignum-lean-port-and-s2n-bignum-hol-light-comparison`

  Verify with:
    /usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M768 \
      reports/cslib-bignum-lean-port-and-s2n-bignum-hol-light-comparison/support/cslib_bignum_component_and_ensures_probe.lean

  Contents:
  1. Faithful standalone mechanization of `cslib-community/bignum` (`92dc3ee58280db51bbbb4dd51b85a91abd0178ba`)
     `Component` lens algebra (`ReadOverWrite`, `WeakReadOverWrite`, `WriteOverRead`,
     `WriteOverWrite`, `Valid`, `WeaklyValid`, `StronglyValid`, `ExtensionallyValid`,
     `Orthogonal` with heterogeneous symmetry fix, `compose` (`:>`), `entirety`, `element`,
     `rvalue`, `through`, `zerotop32`, `bitelement`), plus `Relation.Seq` (`,,`), `Assign` (`≔`),
     `Assigns`, `MayChange`, and the missing `Orthogonal` frame-preservation theorems
     (`Assigns_preserves_orthogonal`, `MayChange_preserves_orthogonal`, and heterogeneous
     `Seq_preserves_read`).
  2. Primary-source diagnosis of `BignumTest/Tutorial/Simple.lean` at `92dc3ee58`:
     proof that `UpstreamDecode.decode` returns `none` on both words of `simple`
     (`0x8b000022` `add x2, x1, x0` and `0xcb010042` `sub x2, x2, x1`) because
     `Bignum/Arm/Decode.lean` implements only Add/subtract (immediate) (`100010`) and omits
     Add/subtract (shifted register) (`01011`), rendering `simple_spec` unprovable (`¬ ∃ s', upstreamArm s s'`);
     followed by an extended decoder `FixedDecode.decode` and a complete, zero-`sorry` proof
     of `simple_spec` (`simple_spec_proven`) and its orthogonal callee-saved/flags frame corollary.
  3. Mechanization of `UArchEvent`, `containedModulo64`, `memaccessInbounds`, step-indexed
     `EventuallyN` / `EnsuresN` (`s2n-bignum/common/relational_n.ml`), and the end-to-end
     Anneal `SmallStepMachine` / `Language.SpecOn` bridge theorem (`ensuresN_safety_refines_anneal_specOn`),
     paired with a negative control (`mayChange_alone_cannot_exclude_unauthorized_load`) proving why
     `Ensures` + `MayChange` without `Safety` (`memaccessInbounds`) is insufficient for Anneal's
     MIR-to-assembly memory-safety boundary (`Issue #102`).
-/

namespace CslibBignumStudy

/-- Standalone replacement for `Batteries`'s `Function.update` (`Bignum` imports `Batteries`). -/
def funcUpdate {α : Type u} {β : Type v} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x ↦ if x = a then b else f x

@[simp]
theorem funcUpdate_self {α : Type u} {β : Type v} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    funcUpdate f a b a = b := by
  simp [funcUpdate]

@[simp]
theorem funcUpdate_ne {α : Type u} {β : Type v} [DecidableEq α] (f : α → β) {a x : α} (b : β)
    (h : x ≠ a) : funcUpdate f a b x = f x := by
  simp [funcUpdate, h]

@[simp]
theorem funcUpdate_idem {α : Type u} {β : Type v} [DecidableEq α] (f : α → β) (a : α) (b₁ b₂ : β) :
    funcUpdate (funcUpdate f a b₁) a b₂ = funcUpdate f a b₂ := by
  funext x
  by_cases h : x = a <;> simp [funcUpdate, h]

@[simp]
theorem funcUpdate_eq_self {α : Type u} {β : Type v} [DecidableEq α] (f : α → β) (a : α) :
    funcUpdate f a (f a) = f := by
  funext x
  by_cases h : x = a
  · subst h; simp [funcUpdate]
  · simp [funcUpdate, h]

/-! ## Part 1: `Component` Lens Hierarchy & Relational Frame Algebra -/

/-- Port of `Bignum/Component/Basic.lean`: `Component α β` state lens. -/
structure Component (α : Type u) (β : Type v) where
  read : α → β
  write : β → α → α

namespace Component

class ReadOverWrite (cp : Component α β) : Prop where
  read_write (b : β) (a : α) : cp.read (cp.write b a) = b

class WeakReadOverWrite (cp : Component α β) : Prop where
  read_write : ∃ (f : β → β), ∀ (b : β) (a : α), cp.read (cp.write b a) = f b

class WriteOverRead (cp : Component α β) : Prop where
  write_read (a : α) : cp.write (cp.read a) a = a

class WriteOverWrite (cp : Component α β) : Prop where
  write_write (b₁ b₂ : β) (a : α) : cp.write b₂ (cp.write b₁ a) = cp.write b₂ a

class Valid (cp : Component α β) : Prop extends
  cp.ReadOverWrite, cp.WriteOverWrite

class WeaklyValid (cp : Component α β) : Prop extends
  cp.WeakReadOverWrite, cp.WriteOverWrite

class StronglyValid (cp : Component α β) : Prop extends
  cp.Valid, cp.WriteOverRead

class ExtensionallyValid (cp : Component α β) : Prop extends
  cp.WeaklyValid, cp.WriteOverRead

/-- Port of `Bignum/Component/Basic.lean`: `Orthogonal cp₁ cp₂`.
    Note that `cp₁ : Component α β` and `cp₂ : Component α γ` may have distinct value types `β` and `γ`. -/
class Orthogonal (cp₁ : Component α β) (cp₂ : Component α γ) : Prop where
  write_write (b : β) (c : γ) (a : α) :
    cp₁.write b (cp₂.write c a) = cp₂.write c (cp₁.write b a)
  read_write_left (b : β) (a : α) : cp₂.read (cp₁.write b a) = cp₂.read a
  read_write_right (c : γ) (a : α) : cp₁.read (cp₂.write c a) = cp₁.read a

/-- Heterogeneous symmetry of `Orthogonal`.
    In upstream `Bignum/Component/Basic.lean:111`, `Orthogonal.symm` is accidentally restricted
    to `cp₁ cp₂ : Component α β` (identical value type `β`). Here we state and prove it for
    arbitrary `β : Type v` and `γ : Type w`. -/
theorem Orthogonal.symm {cp₁ : Component α β} {cp₂ : Component α γ}
    (h : Orthogonal cp₁ cp₂) : Orthogonal cp₂ cp₁ where
  write_write c b a := (h.write_write b c a).symm
  read_write_left c a := h.read_write_right c a
  read_write_right b a := h.read_write_left b a

def compose (cp₁ : Component α β) (cp₂ : Component β γ) : Component α γ where
  read a := cp₂.read (cp₁.read a)
  write c a := cp₁.write (cp₂.write c (cp₁.read a)) a

infixl:55 " :> " => Component.compose

def entirety : Component α α where
  read := id
  write a _ := a

theorem compose_assoc (cp₁ : Component α β) (cp₂ : Component β γ) (cp₃ : Component γ δ) :
    cp₁ :> cp₂ :> cp₃ = cp₁ :> (cp₂ :> cp₃) := rfl

theorem compose_entirety_left (cp : Component α β) : entirety :> cp = cp := rfl
theorem compose_entirety_right (cp : Component α β) : cp :> entirety = cp := rfl

instance [h₁ : ReadOverWrite cp₁] [h₂ : ReadOverWrite cp₂] : ReadOverWrite (cp₁ :> cp₂) where
  read_write c a := by simp only [compose, h₁.read_write, h₂.read_write]

instance [h₁ : WriteOverRead cp₁] [h₂ : WriteOverRead cp₂] : WriteOverRead (cp₁ :> cp₂) where
  write_read a := by simp only [compose, h₂.write_read, h₁.write_read]

instance [h₁ : ReadOverWrite cp₁] [h₂ : WriteOverWrite cp₁] [h₃ : WriteOverWrite cp₂] :
    WriteOverWrite (cp₁ :> cp₂) where
  write_write c₁ c₂ a := by simp only [compose, h₁.read_write, h₂.write_write, h₃.write_write]

instance [Valid cp₁] [Valid cp₂] : Valid (cp₁ :> cp₂) where
instance [StronglyValid cp₁] [StronglyValid cp₂] : StronglyValid (cp₁ :> cp₂) where

/-- If `cp₁` and `cp₂` are orthogonal, composing `cp₁` with any sub-component `sub₁`
    remains orthogonal to `cp₂` (and symmetrically on the right). -/
instance orthogonal_compose_left {cp₁ : Component α β} {sub₁ : Component β β'} {cp₂ : Component α γ}
    [h : Orthogonal cp₁ cp₂] : Orthogonal (cp₁ :> sub₁) cp₂ where
  write_write b' c a := by
    simp only [compose, h.read_write_right, h.write_write]
  read_write_left b' a := by
    simp only [compose, h.read_write_left]
  read_write_right c a := by
    simp only [compose, h.read_write_right]

instance orthogonal_compose_right {cp₁ : Component α β} {cp₂ : Component α γ} {sub₂ : Component γ γ'}
    [h : Orthogonal cp₁ cp₂] : Orthogonal cp₁ (cp₂ :> sub₂) where
  write_write b c' a := by
    simp only [compose, h.read_write_left, h.write_write]
  read_write_left b a := by
    simp only [compose, h.read_write_left]
  read_write_right c' a := by
    simp only [compose, h.read_write_right]

/-- Function-table indexing lens (`Bignum/Component/Extra.lean:16`). -/
def element {α : Type u} {β : Type v} [DecidableEq α] (a : α) : Component (α → β) β where
  read f := f a
  write b f := funcUpdate f a b

instance {α : Type u} {β : Type v} [DecidableEq α] {a : α} :
    StronglyValid (element (α := α) (β := β) a) where
  read_write b f := by simp [element]
  write_write b₁ b₂ f := by simp [element]
  write_read f := by simp [element]

theorem element_orthogonal {α : Type u} {β : Type v} [DecidableEq α] {a₁ a₂ : α} (hne : a₁ ≠ a₂) :
    Orthogonal (element (α := α) (β := β) a₁) (element (α := α) (β := β) a₂) where
  write_write b₁ b₂ f := by
    funext x
    simp only [element, funcUpdate]
    split <;> split <;> subst_vars <;> first | rfl | contradiction
  read_write_left b₁ f := by
    simp [element, hne.symm]
  read_write_right b₂ f := by
    simp [element, hne]

/-- Read-only constant lens (`Bignum/Component/Extra.lean:24`), used for `XZR`, `WZR`, and immediates. -/
def rvalue (b : β) : Component α β where
  read _ := b
  write _ a := a

instance {b : β} {cp : Component α γ} : Orthogonal (rvalue b) cp where
  write_write _ _ _ := rfl
  read_write_left _ _ := rfl
  read_write_right _ _ := rfl

/-- Asymmetric read/write adapter (`Bignum/Component/Extra.lean:32`). -/
def through (f : α → β) (g : β → α) : Component α β where
  read := f
  write b _ := g b

/-- 32-bit zero-extending view of a 64-bit register (`Bignum/Component/Extra.lean:87`):
    reading truncates to 32 bits; writing zero-extends to 64 bits (clearing the upper 32 bits). -/
def zerotop32 : Component (BitVec 64) (BitVec 32) :=
  through (BitVec.truncate 32) (BitVec.zeroExtend 64)

/-- Single-bit lens into a bitvector (`Bignum/Component/Extra.lean:45`). -/
def bitelement (i : Fin w) : Component (BitVec w) Bool where
  read bv := bv[i]
  write b bv :=
    let mask := 1#w <<< i.val
    if b then bv ||| mask else bv &&& ~~~mask

end Component

/-- Binary relations on states (`Bignum/Relational/Basic.lean`). -/
abbrev Relation (α : Type u) (β : Type v) := α → β → Prop

namespace Relation

def Seq (r₁ : Relation α β) (r₂ : Relation β γ) : Relation α γ :=
  fun a c ↦ ∃ b, r₁ a b ∧ r₂ b c

infixr:55 " ,, " => Relation.Seq

def Subsumed (r₁ r₂ : Relation α β) : Prop :=
  ∀ a b, r₁ a b → r₂ a b

infix:50 " ⊆ " => Relation.Subsumed

theorem eq_seq (r : Relation α β) : (Eq ,, r) = r := by
  funext a b; simp [Seq]

theorem seq_eq (r : Relation α β) : (r ,, Eq) = r := by
  funext a b; simp [Seq]

theorem seq_assoc (r₁ : Relation α β) (r₂ : Relation β γ) (r₃ : Relation γ δ) :
    ((r₁ ,, r₂) ,, r₃) = (r₁ ,, (r₂ ,, r₃)) := by
  funext a d
  simp only [Seq, eq_iff_iff]
  constructor
  · rintro ⟨c, ⟨b, h₁, h₂⟩, h₃⟩; exact ⟨b, h₁, c, h₂, h₃⟩
  · rintro ⟨b, h₁, c, h₂, h₃⟩; exact ⟨c, ⟨b, h₁, h₂⟩, h₃⟩

/-- Reachability inductive from `Bignum/Relational/Basic.lean` (at commit `92dc3ee58`):
    requires both existence of a successor (`hs`) and universal postcondition reachability
    across all successors (`hss`). -/
inductive Eventually (step : Relation α α) (P : α → Prop) : α → Prop where
  | base {a : α} (ha : P a) : Eventually step P a
  | step {a : α} (hs : ∃ a', step a a') (hss : ∀ a', step a a' → Eventually step P a') :
      Eventually step P a

/-- Relational Hoare judgment from `Bignum/Relational/Basic.lean` (fixed in commit `d05fddf`
    to universally quantify over the initial state `a`). -/
def Ensures (step : Relation α α) (pre post : α → Prop) (frame : Relation α α) : Prop :=
  ∀ a, pre a → Eventually step (fun a' ↦ post a' ∧ frame a a') a

theorem Eventually.mono {step : Relation α α} {P Q : α → Prop}
    (hPQ : ∀ a, P a → Q a) {a : α} (hev : Eventually step P a) :
    Eventually step Q a := by
  induction hev with
  | base ha => exact .base (hPQ _ ha)
  | step hs _ ih => exact .step hs ih

theorem Eventually.trans {step : Relation α α} {P Q : α → Prop} {a : α}
    (h₁ : Eventually step P a) (h₂ : ∀ b, P b → Eventually step Q b) :
    Eventually step Q a := by
  induction h₁ with
  | base ha => exact h₂ _ ha
  | step hs _ ih => exact .step hs ih

theorem ensures_trans {step : Relation α α} {P Q R : α → Prop} {C₁ C₂ : Relation α α}
    (h₁ : Ensures step P Q C₁) (h₂ : Ensures step Q R C₂) :
    Ensures step P R (C₁ ,, C₂) := by
  intro a hP
  refine (h₁ a hP).trans ?_
  rintro b ⟨hQ, hC₁⟩
  refine (h₂ b hQ).mono ?_
  rintro c ⟨hR, hC₂⟩
  exact ⟨hR, b, hC₁, hC₂⟩

theorem ensures_subsumed {step : Relation α α} {P P' Q Q' : α → Prop} {C C' : Relation α α}
    (hP : ∀ a, P' a → P a) (hQ : ∀ a, Q a → Q' a) (hC : C ⊆ C')
    (h : Ensures step P Q C) : Ensures step P' Q' C' := by
  intro a hP'
  refine (h a (hP a hP')).mono ?_
  rintro a' ⟨hQa', hCa'⟩
  exact ⟨hQ a' hQa', hC a a' hCa'⟩

end Relation

namespace Component

/-- Component assignment relation (`Bignum/Component/Relational.lean:16`). -/
def Assign (cp : Component α β) (b : β) : Relation α α :=
  fun a a' ↦ cp.write b a = a'

infix:60 " ≔ " => Component.Assign

/-- Nondeterministic modification of `cp` (`Bignum/Component/Relational.lean:21`). -/
def Assigns (cp : Component α β) : Relation α α :=
  fun a a' ↦ ∃ b, (cp ≔ b) a a'

/-- Frame relation permitting modification of a list of components (`Bignum/Component/Relational.lean:26`). -/
def MayChange : List (Component α β) → Relation α α
  | [] => Eq
  | cp :: cps => cp.Assigns ,, MayChange cps

theorem Assign_zerotop32 (cp : Component α (BitVec 64)) (bv : BitVec 32) :
    ((cp :> zerotop32) ≔ bv) = (cp ≔ bv.zeroExtend 64) := rfl

theorem Assign_subsumed_Assigns (cp : Component α β) (b : β) :
    (cp ≔ b) ⊆ cp.Assigns :=
  fun _ _ h ↦ ⟨b, h⟩

/-- Missing orthogonality lemma 1: modifying `w` via `Assigns` preserves any orthogonal component `cp`. -/
theorem Assigns_preserves_orthogonal {cp : Component α β} {w : Component α γ}
    (horth : Orthogonal cp w) {a a' : α} (h : w.Assigns a a') :
    cp.read a' = cp.read a := by
  rcases h with ⟨c, rfl⟩
  exact horth.read_write_right c a

/-- Missing orthogonality lemma 2: `MayChange cps` preserves any component `cp` that is
    orthogonal to every component in `cps`. -/
theorem MayChange_preserves_orthogonal {cp : Component α β} {cps : List (Component α γ)}
    (horth : ∀ w ∈ cps, Orthogonal cp w) {a a' : α} (h : MayChange cps a a') :
    cp.read a' = cp.read a := by
  induction cps generalizing a with
  | nil =>
    cases h
    rfl
  | cons w ws ih =>
    rcases h with ⟨mid, hw, hws⟩
    have hmid : cp.read mid = cp.read a :=
      Assigns_preserves_orthogonal (horth w (.head ws)) hw
    have hend : cp.read a' = cp.read mid :=
      ih (fun w' hw' ↦ horth w' (.tail w hw')) hws
    exact hend.trans hmid

/-- Missing orthogonality lemma 3: Sequential composition of heterogeneous `MayChange` frames
    (e.g., 64-bit register `MayChange` followed by flag `MayChange` and event `MayChange`)
    preserves any component orthogonal to each frame. -/
theorem Seq_preserves_read {cp : Component α β} {r₁ r₂ : Relation α α}
    (h₁ : ∀ a b, r₁ a b → cp.read b = cp.read a)
    (h₂ : ∀ b c, r₂ b c → cp.read c = cp.read b)
    {a c : α} (h : (r₁ ,, r₂) a c) :
    cp.read c = cp.read a := by
  rcases h with ⟨b, hr₁, hr₂⟩
  exact (h₂ b c hr₂).trans (h₁ a b hr₁)

end Component

/-! ## Part 2: Memory, AArch64 State, the `Simple.lean` Decode Bug, and Full Proof of `simple_spec` -/

abbrev Byte := BitVec 8
abbrev ByteList := List Byte
abbrev Memory (w : Nat) := BitVec w → Byte

namespace ByteList

def ofNatLE : Nat → Nat → ByteList
  | 0, _ => []
  | k + 1, n => BitVec.ofNat 8 (n % 256) :: ofNatLE k (n / 256)

def toNatLE : ByteList → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * toNatLE bs

@[simp]
theorem length_ofNatLE (k n : Nat) : (ofNatLE k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [ofNatLE, ih]

end ByteList

namespace Memory

def readBytesLE (mem : Memory w) (addr : BitVec w) : Nat → ByteList
  | 0 => []
  | k + 1 => mem addr :: readBytesLE mem (addr + 1#w) k

def writeBytesLE (mem : Memory w) (addr : BitVec w) : ByteList → Memory w
  | [] => mem
  | b :: bs => writeBytesLE (funcUpdate mem addr b) (addr + 1#w) bs

def bytesLE (addr : BitVec w) (len : Nat) : Component (Memory w) ByteList where
  read mem := mem.readBytesLE addr len
  write bs mem := mem.writeBytesLE addr bs

def AlignedBytesLoadedLE (mem : Memory w) (addr : BitVec w) (bs : ByteList) : Prop :=
  4 ∣ addr.toNat ∧ mem.readBytesLE addr bs.length = bs

theorem add_one_add_ofNat (addr : BitVec w) (k : Nat) :
    (addr + 1#w) + BitVec.ofNat w k = addr + BitVec.ofNat w (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_assoc]
  rw [Nat.add_comm 1 k]

theorem readBytesLE_append (mem : Memory w) (addr : BitVec w) (k₁ k₂ : Nat) :
    mem.readBytesLE addr (k₁ + k₂) =
      mem.readBytesLE addr k₁ ++ mem.readBytesLE (addr + BitVec.ofNat w k₁) k₂ := by
  induction k₁ generalizing addr with
  | zero =>
    simp [readBytesLE]
  | succ k₁ ih =>
    simp only [Nat.succ_add, readBytesLE, List.cons_append, ih (addr + 1#w), add_one_add_ofNat]

end Memory

/-- Microarchitectural leakage/safety events (`Bignum/Safety/Basic.lean` and `s2n-bignum/common/safety.ml`). -/
inductive UArchEvent (w : Nat) : Type where
  | EventLoad (addr : BitVec w) (size : Nat)
  | EventStore (addr : BitVec w) (size : Nat)
  | EventJump (src dst : BitVec w)
  deriving DecidableEq, Repr

namespace Arm

/-- Port of `Bignum/Arm/State.lean`: AArch64 architectural state. -/
structure State where
  _pc : BitVec 64
  _regs : BitVec 5 → BitVec 64
  _sregs : BitVec 5 → BitVec 128
  _flags : BitVec 4
  _mem : Memory 64
  _events : List (UArchEvent 64)

namespace State

def PC : Component State (BitVec 64) where
  read s := s._pc
  write v s := { s with _pc := v }

def regs : Component State (BitVec 5 → BitVec 64) where
  read s := s._regs
  write v s := { s with _regs := v }

def sregs : Component State (BitVec 5 → BitVec 128) where
  read s := s._sregs
  write v s := { s with _sregs := v }

def flags : Component State (BitVec 4) where
  read s := s._flags
  write v s := { s with _flags := v }

def mem : Component State (Memory 64) where
  read s := s._mem
  write v s := { s with _mem := v }

def events : Component State (List (UArchEvent 64)) where
  read s := s._events
  write v s := { s with _events := v }

def XREG (i : BitVec 5) : Component State (BitVec 64) := regs :> Component.element i
def WREG (i : BitVec 5) : Component State (BitVec 32) := XREG i :> Component.zerotop32

def XREG' (i : BitVec 5) : Component State (BitVec 64) :=
  if i == 31#5 then .rvalue 0#64 else XREG i

def WREG' (i : BitVec 5) : Component State (BitVec 32) :=
  if i == 31#5 then .rvalue 0#32 else WREG i

abbrev X0  : Component State (BitVec 64) := XREG  0#5
abbrev X1  : Component State (BitVec 64) := XREG  1#5
abbrev X2  : Component State (BitVec 64) := XREG  2#5
abbrev X19 : Component State (BitVec 64) := XREG 19#5
abbrev X30 : Component State (BitVec 64) := XREG 30#5
abbrev SP  : Component State (BitVec 64) := XREG 31#5
abbrev XZR : Component State (BitVec 64) := .rvalue 0#64

def NF : Component State Bool := flags :> .bitelement ⟨3, by decide⟩
def ZF : Component State Bool := flags :> .bitelement ⟨2, by decide⟩
def CF : Component State Bool := flags :> .bitelement ⟨1, by decide⟩
def VF : Component State Bool := flags :> .bitelement ⟨0, by decide⟩

def read (s : State) (cp : Component State β) : β := cp.read s
def write (s : State) (cp : Component State β) (b : β) : State := cp.write b s

def AlignedBytesLoaded (s : State) (addr : BitVec 64) (bs : ByteList) : Prop :=
  s._mem.AlignedBytesLoadedLE addr bs

instance : Component.StronglyValid PC where
  read_write _ _ := rfl
  write_write _ _ _ := rfl
  write_read _ := rfl

instance : Component.StronglyValid regs where
  read_write _ _ := rfl
  write_write _ _ _ := rfl
  write_read _ := rfl

instance : Component.StronglyValid flags where
  read_write _ _ := rfl
  write_write _ _ _ := rfl
  write_read _ := rfl

instance : Component.StronglyValid mem where
  read_write _ _ := rfl
  write_write _ _ _ := rfl
  write_read _ := rfl

instance : Component.StronglyValid events where
  read_write _ _ := rfl
  write_write _ _ _ := rfl
  write_read _ := rfl

instance {i : BitVec 5} : Component.Orthogonal (XREG i) PC where
  write_write _ _ _ := rfl
  read_write_left _ _ := rfl
  read_write_right _ _ := rfl

instance {i : BitVec 5} : Component.Orthogonal flags (XREG i) where
  write_write _ _ _ := rfl
  read_write_left _ _ := rfl
  read_write_right _ _ := rfl

instance : Component.Orthogonal flags PC where
  write_write _ _ _ := rfl
  read_write_left _ _ := rfl
  read_write_right _ _ := rfl

instance {i : BitVec 5} : Component.Orthogonal (XREG i) events where
  write_write _ _ _ := rfl
  read_write_left _ _ := rfl
  read_write_right _ _ := rfl

instance : Component.Orthogonal flags events where
  write_write _ _ _ := rfl
  read_write_left _ _ := rfl
  read_write_right _ _ := rfl

theorem xreg_orthogonal {i j : BitVec 5} (hne : i ≠ j) :
    Component.Orthogonal (XREG i) (XREG j) := by
  have helem : Component.Orthogonal (Component.element (β := BitVec 64) i) (Component.element j) :=
    Component.element_orthogonal hne
  constructor
  · intro b₁ b₂ s
    simp only [XREG, Component.compose, regs, helem.write_write]
  · intro b₁ s
    simp only [XREG, Component.compose, regs, helem.read_write_left]
  · intro b₂ s
    simp only [XREG, Component.compose, regs, helem.read_write_right]

end State

/-! ### Port of `Bignum/Arm/Instruction.lean`: `ADD`, `SUB`, `LDR64`, `STR64` -/

namespace Instruction

def ADD (Rd Rn Rm : Component State (BitVec w)) : Relation State State :=
  fun s s' ↦
    let n := s.read Rn
    let m := s.read Rm
    (Rd ≔ (n + m)) s s'

def SUB (Rd Rn Rm : Component State (BitVec w)) : Relation State State :=
  fun s s' ↦
    let n := s.read Rn
    let m := s.read Rm
    (Rd ≔ (n - m)) s s'

/-- 64-bit unsigned-offset `LDR` emitting `EventLoad` (`s2n-bignum/arm/proofs/instruction.ml:2944`). -/
def LDR64 (Rt Rn : Component State (BitVec 64)) (offBytes : BitVec 64) : Relation State State :=
  fun s s' ↦
    let addr := s.read Rn + offBytes
    let val := BitVec.ofNat 64 (ByteList.toNatLE (s._mem.readBytesLE addr 8))
    ((Rt ≔ val) ,, (State.events ≔ (.EventLoad addr 8 :: s.read State.events))) s s'

/-- 64-bit unsigned-offset `STR` emitting `EventStore` (`s2n-bignum/arm/proofs/instruction.ml:2959`). -/
def STR64 (Rt Rn : Component State (BitVec 64)) (offBytes : BitVec 64) : Relation State State :=
  fun s s' ↦
    let addr := s.read Rn + offBytes
    let bytes := ByteList.ofNatLE 8 (s.read Rt).toNat
    (((State.mem :> Memory.bytesLE addr 8) ≔ bytes) ,,
      (State.events ≔ (.EventStore addr 8 :: s.read State.events))) s s'

end Instruction

/-! ### Exact reproduction of upstream `Bignum/Arm/Decode.lean` at commit `92dc3ee58` -/

namespace UpstreamDecode

def addOp : Bool → Bool → (Component State (BitVec w) → Component State (BitVec w) →
    Component State (BitVec w) → Relation State State)
  | false, false => Instruction.ADD
  | true,  false => Instruction.SUB
  | _,     true  => fun _ _ _ _ _ ↦ False

def decode (bv : BitVec 32) : Option (Relation State State) :=
  if bv.extractLsb' 23 6 == 0b100010#6 then
    let sf    := bv.extractLsb' 31 1 == 1#1
    let op    := bv.extractLsb' 30 1 == 1#1
    let S     := bv.extractLsb' 29 1 == 1#1
    let sh    := bv.extractLsb' 22 1
    let imm12 := bv.extractLsb' 10 12
    let Rn    := bv.extractLsb' 5 5
    let Rd    := bv.extractLsb' 0 5
    let val : Nat := imm12.toNat <<< (12 * sh.toNat)
    if sf then
      let Rd64 := if S then State.XREG' Rd else State.XREG Rd
      some (addOp op S Rd64 (State.XREG Rn) (.rvalue (.ofNat 64 val)))
    else
      let Rd32 := if S then State.WREG' Rd else State.WREG Rd
      some (addOp op S Rd32 (State.WREG Rn) (.rvalue (.ofNat 32 val)))
  else
    none

end UpstreamDecode

/-- Upstream `State.decode` and `arm` step relation (`Bignum/Arm/Semantics.lean`) using `UpstreamDecode`. -/
structure UpstreamStateDecode (s : State) (addr : BitVec 64) : Type where
  instr : Relation State State
  data : BitVec 32
  loaded : s.AlignedBytesLoaded addr (.ofNatLE 4 data.toNat)
  decode : UpstreamDecode.decode data = some instr

def upstreamArm : Relation State State :=
  fun s s' ↦ ∃ d : UpstreamStateDecode s (s.read State.PC),
    ((State.PC ≔ (s.read State.PC + 4#64)) ,, d.instr) s s'

/-- The exact 8-byte program from `BignumTest/Tutorial/Simple.lean:12-14`:
    `0x8b000022` (`add x2, x1, x0`) followed by `0xcb010042` (`sub x2, x2, x1`). -/
def simple : ByteList :=
  ByteList.ofNatLE 4 0x8b000022 ++ ByteList.ofNatLE 4 0xcb010042

/-- Diagnosis Theorem 1: Upstream `Decode.decode` returns `none` on `0x8b000022` (`add x2, x1, x0`)
    and `0xcb010042` (`sub x2, x2, x1`) because their bits `[28:23]` are `0b010110` (shifted register),
    not `0b100010` (immediate). -/
theorem upstream_decode_simple_word0_is_none :
    UpstreamDecode.decode 0x8b000022#32 = none := rfl

theorem upstream_decode_simple_word1_is_none :
    UpstreamDecode.decode 0xcb010042#32 = none := rfl

theorem toNatLE_ofNatLE_four (w : BitVec 32) :
    ByteList.toNatLE (ByteList.ofNatLE 4 w.toNat) = w.toNat := by
  have hlt : w.toNat < 4294967296 := w.isLt
  simp [ByteList.ofNatLE, ByteList.toNatLE, BitVec.toNat_ofNat]
  omega

theorem ofNatLE_four_injective {w₁ w₂ : BitVec 32}
    (h : ByteList.ofNatLE 4 w₁.toNat = ByteList.ofNatLE 4 w₂.toNat) :
    w₁ = w₂ := by
  apply BitVec.eq_of_toNat_eq
  have h' := congrArg ByteList.toNatLE h
  simpa [toNatLE_ofNatLE_four] using h'

/-- Diagnosis Theorem 2: Under upstream `Bignum/Arm/Decode.lean` at `92dc3ee58`, any state `s`
    with `simple` loaded at `PC` has NO `upstreamArm` successor (`¬ ∃ s', upstreamArm s s'`),
    proving that `BignumTest/Tutorial/Simple.lean`'s `simple_spec` is unprovable without
    adding the Add/subtract (shifted register) decoding arm. -/
theorem upstream_simple_stuck_at_entry (s : State) (pc : Nat)
    (hload : s.AlignedBytesLoaded (BitVec.ofNat 64 pc) simple)
    (hpc : s.read State.PC = BitVec.ofNat 64 pc) :
    ¬ ∃ s', upstreamArm s s' := by
  rintro ⟨s', d, _⟩
  have hpc_load : s.AlignedBytesLoaded (s.read State.PC) simple := hpc ▸ hload
  rcases hpc_load with ⟨_, hbytes⟩
  have hsplit := s._mem.readBytesLE_append (s.read State.PC) 4 4
  change s._mem.readBytesLE (s.read State.PC) 8 = simple at hbytes
  rw [hsplit] at hbytes
  have hlen : (s._mem.readBytesLE (s.read State.PC) 4).length =
      (ByteList.ofNatLE 4 (0x8b000022#32).toNat).length := by
    simp [Memory.readBytesLE, ByteList.ofNatLE]
  have hword0 : s._mem.readBytesLE (s.read State.PC) 4 =
      ByteList.ofNatLE 4 (0x8b000022#32).toNat :=
    (List.append_inj hbytes hlen).1
  have hd_bytes : s._mem.readBytesLE (s.read State.PC) 4 = ByteList.ofNatLE 4 d.data.toNat := by
    simpa [ByteList.length_ofNatLE] using d.loaded.2
  have hdata_eq : d.data = 0x8b000022#32 :=
    ofNatLE_four_injective (hd_bytes.symm.trans hword0)
  have hdec := d.decode
  rw [hdata_eq, upstream_decode_simple_word0_is_none] at hdec
  cases hdec

/-! ### Extended Decoder `FixedDecode.decode` and Zero-`sorry` Proof of `simple_spec` -/

namespace FixedDecode

def decode (bv : BitVec 32) : Option (Relation State State) :=
  if bv.extractLsb' 23 6 == 0b100010#6 then
    -- Add/subtract (immediate)
    let sf    := bv.extractLsb' 31 1 == 1#1
    let op    := bv.extractLsb' 30 1 == 1#1
    let S     := bv.extractLsb' 29 1 == 1#1
    let sh    := bv.extractLsb' 22 1
    let imm12 := bv.extractLsb' 10 12
    let Rn    := bv.extractLsb' 5 5
    let Rd    := bv.extractLsb' 0 5
    let val : Nat := imm12.toNat <<< (12 * sh.toNat)
    if S then none
    else if sf then
      some (UpstreamDecode.addOp op false (State.XREG Rd) (State.XREG Rn) (.rvalue (.ofNat 64 val)))
    else
      some (UpstreamDecode.addOp op false (State.WREG Rd) (State.WREG Rn) (.rvalue (.ofNat 32 val)))
  else if bv.extractLsb' 21 8 == 0b01011000#8 && bv.extractLsb' 10 6 == 0#6 then
    -- Add/subtract (shifted register, LSL #0)
    let sf := bv.extractLsb' 31 1 == 1#1
    let op := bv.extractLsb' 30 1 == 1#1
    let S  := bv.extractLsb' 29 1 == 1#1
    let Rm := bv.extractLsb' 16 5
    let Rn := bv.extractLsb' 5 5
    let Rd := bv.extractLsb' 0 5
    if S then none
    else if sf then
      some (UpstreamDecode.addOp op false (State.XREG' Rd) (State.XREG' Rn) (State.XREG' Rm))
    else
      some (UpstreamDecode.addOp op false (State.WREG' Rd) (State.WREG' Rn) (State.WREG' Rm))
  else if bv.extractLsb' 22 10 == 0b1111100101#10 then
    -- 64-bit LDR (unsigned offset)
    let imm12 := bv.extractLsb' 10 12
    let Rn    := bv.extractLsb' 5 5
    let Rt    := bv.extractLsb' 0 5
    some (Instruction.LDR64 (State.XREG' Rt) (State.XREG Rn) (.ofNat 64 (imm12.toNat * 8)))
  else if bv.extractLsb' 22 10 == 0b1111100100#10 then
    -- 64-bit STR (unsigned offset)
    let imm12 := bv.extractLsb' 10 12
    let Rn    := bv.extractLsb' 5 5
    let Rt    := bv.extractLsb' 0 5
    some (Instruction.STR64 (State.XREG' Rt) (State.XREG Rn) (.ofNat 64 (imm12.toNat * 8)))
  else
    none

theorem decode_add_x2_x1_x0 :
    decode 0x8b000022#32 = some (Instruction.ADD State.X2 State.X1 State.X0) := rfl

theorem decode_sub_x2_x2_x1 :
    decode 0xcb010042#32 = some (Instruction.SUB State.X2 State.X2 State.X1) := rfl

/-- `0xf9400022` = `ldr x2, [x1, #0]` -/
theorem decode_ldr_x2_x1_0 :
    decode 0xf9400022#32 = some (Instruction.LDR64 State.X2 State.X1 0#64) := rfl

/-- `0xf9000022` = `str x2, [x1, #0]` -/
theorem decode_str_x2_x1_0 :
    decode 0xf9000022#32 = some (Instruction.STR64 State.X2 State.X1 0#64) := rfl

end FixedDecode

structure FixedStateDecode (s : State) (addr : BitVec 64) : Type where
  instr : Relation State State
  data : BitVec 32
  loaded : s.AlignedBytesLoaded addr (.ofNatLE 4 data.toNat)
  decode : FixedDecode.decode data = some instr

def fixedArm : Relation State State :=
  fun s s' ↦ ∃ d : FixedStateDecode s (s.read State.PC),
    ((State.PC ≔ (s.read State.PC + 4#64)) ,, d.instr) s s'

/-- Characterization of a single `fixedArm` step when a 4-byte instruction word `w` is loaded at `PC`. -/
theorem fixedArm_step_iff_of_loaded (s s' : State) {addr : BitVec 64} {w : BitVec 32}
    {instr : Relation State State}
    (hpc : s.read State.PC = addr)
    (hload : s.AlignedBytesLoaded addr (ByteList.ofNatLE 4 w.toNat))
    (hdec : FixedDecode.decode w = some instr) :
    fixedArm s s' ↔ ((State.PC ≔ (addr + 4#64)) ,, instr) s s' := by
  constructor
  · rintro ⟨d, hseq⟩
    have hd_bytes : s._mem.readBytesLE addr 4 = ByteList.ofNatLE 4 d.data.toNat := by
      simpa [hpc, ByteList.length_ofNatLE] using d.loaded.2
    have hw_bytes : s._mem.readBytesLE addr 4 = ByteList.ofNatLE 4 w.toNat := by
      simpa [ByteList.length_ofNatLE] using hload.2
    have hdata : d.data = w := ofNatLE_four_injective (hd_bytes.symm.trans hw_bytes)
    have hinstr : d.instr = instr := by
      have h1 := d.decode
      rw [hdata, hdec] at h1
      exact Option.some.inj h1.symm
    simpa [hpc, hinstr] using hseq
  · intro hseq
    refine ⟨⟨instr, w, hpc.symm ▸ hload, hdec⟩, ?_⟩
    simpa [hpc] using hseq

theorem dvd_four_add_four {addr : BitVec 64} (h : 4 ∣ addr.toNat) :
    4 ∣ (addr + 4#64).toNat := by
  have h1 : (addr + 4#64).toNat = (addr.toNat + 4) % 18446744073709551616 := by
    simp [BitVec.toNat_add]
  rw [h1]
  omega

theorem split_simple_loaded {s : State} {addr : BitVec 64}
    (hload : s.AlignedBytesLoaded addr simple) :
    s.AlignedBytesLoaded addr (ByteList.ofNatLE 4 (0x8b000022#32).toNat) ∧
    s.AlignedBytesLoaded (addr + 4#64) (ByteList.ofNatLE 4 (0xcb010042#32).toNat) := by
  rcases hload with ⟨hdvd, hbytes⟩
  have hsplit := s._mem.readBytesLE_append addr 4 4
  change s._mem.readBytesLE addr 8 = simple at hbytes
  rw [hsplit] at hbytes
  have hlen : (s._mem.readBytesLE addr 4).length =
      (ByteList.ofNatLE 4 (0x8b000022#32).toNat).length := by
    simp [Memory.readBytesLE, ByteList.ofNatLE]
  have hinj := List.append_inj hbytes hlen
  refine ⟨⟨hdvd, ?_⟩, ⟨dvd_four_add_four hdvd, ?_⟩⟩
  · simpa [ByteList.length_ofNatLE] using hinj.1
  · simpa [ByteList.length_ofNatLE] using hinj.2

/-- Complete, zero-`sorry` proof of `simple_spec` from `BignumTest/Tutorial/Simple.lean:16-28`
    against `fixedArm`. -/
theorem simple_spec_proven (pc : Nat) (a b : BitVec 64) :
    Relation.Ensures fixedArm
      (fun s ↦ s.AlignedBytesLoaded (BitVec.ofNat 64 pc) simple
        ∧ s.read State.PC = BitVec.ofNat 64 pc
        ∧ s.read State.X0 = a
        ∧ s.read State.X1 = b)
      (fun s ↦ s.read State.PC = BitVec.ofNat 64 (pc + 8)
        ∧ s.read State.X2 = a)
      (Component.MayChange [State.PC, State.X2]) := by
  intro s₀ ⟨hload, hpc, hx0, hx1⟩
  rcases split_simple_loaded hload with ⟨hload0, hload1⟩
  let addr0 := BitVec.ofNat 64 pc
  let s₁ := s₀.write State.PC (addr0 + 4#64) |>.write State.X2 (b + a)
  have hstep1 : fixedArm s₀ s₁ := by
    rw [fixedArm_step_iff_of_loaded s₀ s₁ hpc hload0 FixedDecode.decode_add_x2_x1_x0]
    refine ⟨s₀.write State.PC (addr0 + 4#64), rfl, ?_⟩
    simp [s₁, addr0, Instruction.ADD, Component.Assign, State.read, State.write, State.X0, State.X1, State.X2,
      State.XREG, State.PC, Component.compose, State.regs, Component.element] at hx0 hx1 ⊢
    rw [hx1, hx0]
  refine Relation.Eventually.step ⟨s₁, hstep1⟩ ?_
  intro s₁' hs₁'
  rw [fixedArm_step_iff_of_loaded s₀ s₁' hpc hload0 FixedDecode.decode_add_x2_x1_x0] at hs₁'
  rcases hs₁' with ⟨smid, rfl, hadd⟩
  have hs₁'_eq : s₁' = s₁ := by
    simp [s₁, addr0, Instruction.ADD, Component.Assign, State.read, State.write, State.X0, State.X1, State.X2,
      State.XREG, State.PC, Component.compose, State.regs, Component.element] at hx0 hx1 hadd ⊢
    rw [← hadd, hx1, hx0]
  subst hs₁'_eq
  have hload1_s₁ : s₁.AlignedBytesLoaded (addr0 + 4#64) (ByteList.ofNatLE 4 (0xcb010042#32).toNat) :=
    hload1
  have hpc1 : s₁.read State.PC = addr0 + 4#64 := rfl
  let s₂ := s₁.write State.PC ((addr0 + 4#64) + 4#64) |>.write State.X2 ((b + a) - b)
  have hx1' : s₀._regs 1#5 = b := hx1
  have hstep2 : fixedArm s₁ s₂ := by
    rw [fixedArm_step_iff_of_loaded s₁ s₂ hpc1 hload1_s₁ FixedDecode.decode_sub_x2_x2_x1]
    refine ⟨s₁.write State.PC ((addr0 + 4#64) + 4#64), rfl, ?_⟩
    have hne12 : (1#5 : BitVec 5) ≠ 2#5 := by decide
    simp [s₁, s₂, Instruction.SUB, Component.Assign, State.read, State.write, State.X1, State.X2,
      State.XREG, State.PC, Component.compose, State.regs, Component.element, hne12, hx1']
  refine Relation.Eventually.step ⟨s₂, hstep2⟩ ?_
  intro s₂' hs₂'
  rw [fixedArm_step_iff_of_loaded s₁ s₂' hpc1 hload1_s₁ FixedDecode.decode_sub_x2_x2_x1] at hs₂'
  rcases hs₂' with ⟨smid2, rfl, hsub⟩
  have hs₂'_eq : s₂' = s₂ := by
    have hne12 : (1#5 : BitVec 5) ≠ 2#5 := by decide
    simp [s₁, s₂, Instruction.SUB, Component.Assign, State.read, State.write, State.X1, State.X2,
      State.XREG, State.PC, Component.compose, State.regs, Component.element, hne12, hx1'] at hsub ⊢
    rw [← hsub]
  subst hs₂'_eq
  refine Relation.Eventually.base ⟨⟨?_, ?_⟩, ?_⟩
  · change (BitVec.ofNat 64 pc + 4#64) + 4#64 = BitVec.ofNat 64 (pc + 8)
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_assoc]
  · change (b + a) - b = a
    bv_omega
  · refine ⟨s₀.write State.PC ((addr0 + 4#64) + 4#64), ⟨(addr0 + 4#64) + 4#64, rfl⟩, ?_⟩
    refine ⟨s₂, ⟨(b + a) - b, ?_⟩, rfl⟩
    simp [s₂, s₁, Component.Assign, State.write, State.PC, State.X2, State.XREG,
      Component.compose, State.regs, Component.element]

/-- Frame preservation corollary for `simple_spec`: any state related by `MayChange [PC, X2]`
    automatically preserves callee-saved registers (`X19`, `SP`) and condition flags (`flags`)
    via `Component.MayChange_preserves_orthogonal`. -/
theorem simple_frame_preserves_abi_state {s s' : State}
    (hframe : Component.MayChange [State.PC, State.X2] s s') :
    s'.read State.X19 = s.read State.X19 ∧
    s'.read State.SP = s.read State.SP ∧
    s'.read State.flags = s.read State.flags := by
  refine ⟨?_, ?_, ?_⟩
  · apply Component.MayChange_preserves_orthogonal _ hframe
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · infer_instance
    · exact State.xreg_orthogonal (by decide)
  · apply Component.MayChange_preserves_orthogonal _ hframe
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · infer_instance
    · exact State.xreg_orthogonal (by decide)
  · apply Component.MayChange_preserves_orthogonal _ hframe
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · infer_instance
    · infer_instance

end Arm

/-! ## Part 3: Step-Indexed `EnsuresN`, `Safety` (`memaccessInbounds`), and Anneal Bridge Theorem -/

/-- Port of `s2n-bignum/common/safety.ml:142`: `contained_modulo (2^64) (ptr, sz) (base, len)`.
    Checks that `[ptr, ptr + sz)` is contained within `[base, base + len)` in 64-bit modular
    address arithmetic (handling `sz = 0` vacuously). -/
def containedModulo64 (ptr : BitVec 64) (sz : Nat) (range : BitVec 64 × Nat) : Bool :=
  sz == 0 || (sz ≤ range.2 && (ptr - range.1).toNat + sz ≤ range.2)

/-- Port of `s2n-bignum/common/safety.ml:150`: `memaccess_inbounds events readRanges writeRanges`.
    Every `EventLoad` must fall within at least one allowed read range, and every `EventStore`
    must fall within at least one allowed write range. -/
def memaccessInbounds (evts : List (UArchEvent 64))
    (readRanges writeRanges : List (BitVec 64 × Nat)) : Bool :=
  evts.all fun e ↦
    match e with
    | .EventJump _ _ => true
    | .EventLoad addr sz => readRanges.any (containedModulo64 addr sz)
    | .EventStore addr sz => writeRanges.any (containedModulo64 addr sz)

theorem memaccessInbounds_append (e₁ e₂ : List (UArchEvent 64))
    (rRanges wRanges : List (BitVec 64 × Nat)) :
    memaccessInbounds (e₁ ++ e₂) rRanges wRanges =
      (memaccessInbounds e₁ rRanges wRanges && memaccessInbounds e₂ rRanges wRanges) := by
  simp [memaccessInbounds, List.all_append]

/-- Port of `s2n-bignum/common/relational_n.ml`: `EventuallyN step n P s`. -/
inductive EventuallyN (step : Relation α α) (P : α → Prop) : Nat → α → Prop where
  | zero {a : α} (ha : P a) : EventuallyN step P 0 a
  | succ {n : Nat} {a : α} (hs : ∃ a', step a a')
      (hss : ∀ a', step a a' → EventuallyN step P n a') :
      EventuallyN step P (n + 1) a

/-- Port of `EVENTUALLY_N_EVENTUALLY` (`s2n-bignum/common/relational_n.ml:266`). -/
theorem EventuallyN.toEventually {step : Relation α α} {P : α → Prop} {n : Nat} {a : α}
    (h : EventuallyN step P n a) : Relation.Eventually step P a := by
  induction h with
  | zero ha => exact .base ha
  | succ hs _ ih => exact .step hs ih

/-- Port of `ensures_n` (`s2n-bignum/common/relational_n.ml:348`). -/
def EnsuresN (step : Relation α α) (pre post : α → Prop) (frame : Relation α α)
    (stepCount : α → Nat) : Prop :=
  ∀ a, pre a → EventuallyN step (fun a' ↦ post a' ∧ frame a a') (stepCount a) a

theorem EnsuresN.toEnsures {step : Relation α α} {pre post : α → Prop}
    {frame : Relation α α} {stepCount : α → Nat}
    (h : EnsuresN step pre post frame stepCount) : Relation.Ensures step pre post frame :=
  fun a hpre ↦ (h a hpre).toEventually

/-! ### Anneal Trusted Foundation (`Trusted/Refinement.lean` & `Trusted/StepResult.lean`) -/

def Set (α : Type u) := α → Prop

def Partial (α β : Type) := α → Option β

class Preorder (α : Type u) extends LE α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c

def Behavior (Query Obs : Type) := Query → Set Obs

instance (Query Obs : Type) : Preorder (Behavior Query Obs) where
  le b₁ b₂ := ∀ q o, b₁ q o → b₂ q o
  le_refl _ _ _ h := h
  le_trans _ _ _ h₁ h₂ q o ho := h₂ q o (h₁ q o ho)

inductive Outcome (State : Type) where
  | terminated (final : State)
  | running (current : State)
  | stuck

def Outcome.Satisfies (post : State → Prop) : Outcome State → Prop
  | .terminated final => post final
  | .running _ => True
  | .stuck => False

structure Language (Prog Query Obs : Type) where
  compile : Partial Prog (Behavior Query Obs)

def Language.SpecOn (_L : Language Prog Query (Outcome State))
    (pre : Prog → Prop) [DecidablePred pre] (post : State → Prop) :
    Partial Prog (Behavior Query (Outcome State)) :=
  fun p ↦
    if pre p then
      some (fun _q (o : Outcome State) ↦ Outcome.Satisfies post o)
    else
      none

inductive StepResult (State : Type) where
  | step (next : State)
  | done (final : State)
  | uck

inductive PrefixOutcome (State : Type) where
  | terminated (final : State)
  | exhausted (current : State)
  | uck

def PrefixOutcome.toOutcome : PrefixOutcome State → Outcome State
  | .terminated final => .terminated final
  | .exhausted current => .running current
  | .uck => .stuck

structure SmallStepMachine (Prog State : Type) where
  init : Partial Prog State
  step : State → StepResult State

inductive ReachesPrefix (M : SmallStepMachine Prog State) :
    State → Nat → PrefixOutcome State → Prop where
  | zero (s : State) :
      ReachesPrefix M s 0 (.exhausted s)
  | done (s final : State) (fuel : Nat) :
      M.step s = .done final →
      ReachesPrefix M s (fuel + 1) (.terminated final)
  | uck (s : State) (fuel : Nat) :
      M.step s = .uck →
      ReachesPrefix M s (fuel + 1) .uck
  | step (s next : State) (fuel : Nat) (out : PrefixOutcome State) :
      M.step s = .step next →
      ReachesPrefix M next fuel out →
      ReachesPrefix M s (fuel + 1) out

structure StepQuery where
  steps : Nat

def SmallStepMachine.BehaviorOf (M : SmallStepMachine Prog State) (s₀ : State) :
    Behavior StepQuery (Outcome State) :=
  fun q o ↦ ∃ po, ReachesPrefix M s₀ q.steps po ∧ po.toOutcome = o

def SmallStepMachine.toLanguage (M : SmallStepMachine Prog State) :
    Language Prog StepQuery (Outcome State) where
  compile p := Option.map M.BehaviorOf (M.init p)

/-! ### Anneal Inline/Global Assembly Bridge Contract (`Issue #102`) -/

/-- Contract for an Anneal MIR-to-assembly block (`Issue #102`):
    - `pcExit`: exit PC where control returns to MIR
    - `preservedStateEq`: equality of all ABI-preserved registers/flags (`clobber_abi` / `preserves_flags`)
    - `readableRanges`, `writableRanges`: permitted memory footprints -/
structure AnnealAsmBridgeContract where
  pcExit : BitVec 64
  preservedStateEq : Arm.State → Arm.State → Prop
  readableRanges : List (BitVec 64 × Nat)
  writableRanges : List (BitVec 64 × Nat)

/-- Combined `s2n-bignum` / `cslib-community/bignum` `EnsuresN + Safety` specification for an
    assembly block starting from `s₀`:
    1. Reaches `post s'` and `frame s₀ s'` in `n` steps;
    2. For every intermediate state before step `n`, `s.read PC ≠ pcExit`, and every single step
       emits only in-bounds memory events (`memaccessInbounds`);
    3. At step `n`, `s'.read PC = pcExit`. -/
inductive SafeExecutionN (execStep : Arm.State → Option Arm.State) (c : AnnealAsmBridgeContract)
    (s₀ : Arm.State) (post : Arm.State → Prop) (frame : Relation Arm.State Arm.State) :
    Nat → Arm.State → Prop where
  | exit {s : Arm.State}
      (hpc : s.read Arm.State.PC = c.pcExit)
      (hpost : post s)
      (hframe : frame s₀ s) :
      SafeExecutionN execStep c s₀ post frame 0 s
  | step {n : Nat} {s s' : Arm.State}
      (hpc : s.read Arm.State.PC ≠ c.pcExit)
      (hstep : execStep s = some s')
      (hevts : ∃ newEvts,
        s'.read Arm.State.events = newEvts ++ s.read Arm.State.events ∧
        memaccessInbounds newEvts c.readableRanges c.writableRanges = true)
      (hrest : SafeExecutionN execStep c s₀ post frame n s') :
      SafeExecutionN execStep c s₀ post frame (n + 1) s

/-- Guarded Anneal `SmallStepMachine` for an assembly block under `AnnealAsmBridgeContract`:
    - When `s.read PC == c.pcExit`, checks `c.preservedStateEq s₀ s`: if preserved, returns `.done s`,
      else `.uck` (clobber violation!).
    - When `s.read PC != c.pcExit`, executes `execStep s`: if `none` or if newly emitted events
      violate `memaccessInbounds`, returns `.uck`; otherwise returns `.step s'`. -/
def asmBridgeStep (execStep : Arm.State → Option Arm.State) (c : AnnealAsmBridgeContract)
    [DecidableRel c.preservedStateEq] (s₀ s : Arm.State) : StepResult Arm.State :=
  if s.read Arm.State.PC == c.pcExit then
    if c.preservedStateEq s₀ s then .done s else .uck
  else
    match execStep s with
    | none => .uck
    | some s' =>
      let newCount := (s'.read Arm.State.events).length - (s.read Arm.State.events).length
      let newEvts := (s'.read Arm.State.events).take newCount
      if s'.read Arm.State.events == newEvts ++ s.read Arm.State.events &&
         memaccessInbounds newEvts c.readableRanges c.writableRanges then
        .step s'
      else
        .uck

def asmBridgeMachine (execStep : Arm.State → Option Arm.State) (c : AnnealAsmBridgeContract)
    [DecidableRel c.preservedStateEq] (s₀ : Arm.State) : SmallStepMachine Unit Arm.State where
  init _ := some s₀
  step := asmBridgeStep execStep c s₀

theorem take_append_of_eq {α : Type} (l₁ l₂ : List α) :
    (l₁ ++ l₂).take ((l₁ ++ l₂).length - l₂.length) = l₁ := by
  simp [List.length_append]

/-- Core Prefix-Preservation Lemma: under `SafeExecutionN`, if the `frame` preserves all
    `c.preservedStateEq` components, then for ANY step budget `fuel`, `ReachesPrefix` on
    `asmBridgeMachine` never hits `.uck` and always satisfies `Outcome.Satisfies post`! -/
theorem safeExecutionN_reachesPrefix_satisfies
    (execStep : Arm.State → Option Arm.State) (c : AnnealAsmBridgeContract)
    [DecidableRel c.preservedStateEq]
    {s₀ s : Arm.State} {post : Arm.State → Prop} {frame : Relation Arm.State Arm.State}
    (hframe_pres : ∀ s_end, frame s₀ s_end → c.preservedStateEq s₀ s_end)
    {n : Nat} (hsafe : SafeExecutionN execStep c s₀ post frame n s) :
    ∀ (fuel : Nat) (po : PrefixOutcome Arm.State),
      ReachesPrefix (asmBridgeMachine execStep c s₀) s fuel po →
      po.toOutcome.Satisfies post := by
  induction hsafe with
  | @exit s hpc hpost hframe =>
    intro fuel po hreach
    cases hreach with
    | zero =>
      trivial
    | done _ final _ hstep =>
      have hpres : c.preservedStateEq s₀ s := hframe_pres s hframe
      have hstep_eq : asmBridgeStep execStep c s₀ s = .done s := by
        simp [asmBridgeStep, hpc, hpres]
      change asmBridgeStep execStep c s₀ s = .done final at hstep
      rw [hstep_eq] at hstep
      cases hstep
      exact hpost
    | uck _ _ hstep =>
      have hpres : c.preservedStateEq s₀ s := hframe_pres s hframe
      have hstep_eq : asmBridgeStep execStep c s₀ s = .done s := by
        simp [asmBridgeStep, hpc, hpres]
      change asmBridgeStep execStep c s₀ s = .uck at hstep
      rw [hstep_eq] at hstep
      cases hstep
    | step _ next _ _ hstep _ =>
      have hpres : c.preservedStateEq s₀ s := hframe_pres s hframe
      have hstep_eq : asmBridgeStep execStep c s₀ s = .done s := by
        simp [asmBridgeStep, hpc, hpres]
      change asmBridgeStep execStep c s₀ s = .step next at hstep
      rw [hstep_eq] at hstep
      cases hstep
  | @step n s s' hpc hstep hevts _ ih =>
    rcases hevts with ⟨newEvts, hevts_eq, hinb⟩
    have hstep_eq : asmBridgeStep execStep c s₀ s = .step s' := by
      have hpc_beq : (s.read Arm.State.PC == c.pcExit) = false := beq_false_of_ne hpc
      simp only [asmBridgeStep, hpc_beq, Bool.false_eq_true, ↓reduceIte, hstep]
      have htake : (s'.read Arm.State.events).take
          ((s'.read Arm.State.events).length - (s.read Arm.State.events).length) = newEvts := by
        rw [hevts_eq, take_append_of_eq]
      rw [htake]
      have heq_beq : (s'.read Arm.State.events == newEvts ++ s.read Arm.State.events) = true :=
        beq_iff_eq.mpr hevts_eq
      simp [heq_beq, hinb]
    intro fuel po hreach
    cases hreach with
    | zero =>
      trivial
    | done _ final _ hst =>
      change asmBridgeStep execStep c s₀ s = .done final at hst
      rw [hstep_eq] at hst
      cases hst
    | uck _ _ hst =>
      change asmBridgeStep execStep c s₀ s = .uck at hst
      rw [hstep_eq] at hst
      cases hst
    | step _ next fuel' _ hst hreach' =>
      change asmBridgeStep execStep c s₀ s = .step next at hst
      rw [hstep_eq] at hst
      cases hst
      exact ih fuel' po hreach'

/-- **End-to-End Anneal Bridge Refinement Theorem (`Issue #102`):**
    If an assembly routine has a verified `SafeExecutionN` proof (connecting `EnsuresN` + `MayChange` +
    `memaccessInbounds`) and its `MayChange` `frame` is orthogonal to the ABI-preserved registers/flags
    in `c.preservedStateEq`, then the guarded `asmBridgeMachine` refines Anneal's `Language.SpecOn`
    across ALL finite step budgets `q.steps`. -/
theorem ensuresN_safety_refines_anneal_specOn
    (execStep : Arm.State → Option Arm.State) (c : AnnealAsmBridgeContract)
    [DecidableRel c.preservedStateEq]
    {s₀ : Arm.State} {post : Arm.State → Prop} {frame : Relation Arm.State Arm.State} {n : Nat}
    (hframe_pres : ∀ s_end, frame s₀ s_end → c.preservedStateEq s₀ s_end)
    (hsafe : SafeExecutionN execStep c s₀ post frame n s₀) :
    ∃ bSpec,
      (asmBridgeMachine execStep c s₀).toLanguage.SpecOn (fun _ ↦ True) post () = some bSpec ∧
      (asmBridgeMachine execStep c s₀).BehaviorOf s₀ ≤ bSpec := by
  refine ⟨fun _q (o : Outcome Arm.State) ↦ Outcome.Satisfies post o, rfl, ?_⟩
  intro q o ⟨po, hreach, hpo⟩
  subst hpo
  exact safeExecutionN_reachesPrefix_satisfies execStep c hframe_pres hsafe q.steps po hreach

/-- **Negative Control Theorem:**
    `Ensures` with `MayChange` alone (without `Safety` / `memaccessInbounds`) is UNSOUND as a
    standalone Anneal memory-safety bridge:
    A 1-instruction `LDR X2, [X1, #0]` reading from an unauthorized address `0xdead0000#64`
    satisfies `MayChange [PC, X2] ,, MayChange [events]` and preserves `SP`,
    yet immediately triggers `StepResult.uck` under `asmBridgeStep` when `readableRanges = []`. -/
theorem mayChange_alone_cannot_exclude_unauthorized_load (s₀ : Arm.State)
    (hpc : s₀.read Arm.State.PC = 0x1000#64) :
    let stepFn : Arm.State → Option Arm.State := fun s ↦
      some (s.write Arm.State.PC (s.read Arm.State.PC + 4#64)
            |>.write Arm.State.X2 (BitVec.ofNat 64 (ByteList.toNatLE (s._mem.readBytesLE (s.read Arm.State.X1) 8)))
            |>.write Arm.State.events (.EventLoad (s.read Arm.State.X1) 8 :: s.read Arm.State.events))
    let contract : AnnealAsmBridgeContract := {
      pcExit := 0x1004#64
      preservedStateEq := fun a b ↦ b.read Arm.State.SP = a.read Arm.State.SP
      readableRanges := []
      writableRanges := []
    }
    let s₁ := (stepFn s₀).getD s₀
    -- (1) The transition satisfies the `MayChange [PC, X2] ,, MayChange [events]` frame and preserves SP:
    ((Component.MayChange [Arm.State.PC, Arm.State.X2] ,, Component.MayChange [Arm.State.events]) s₀ s₁ ∧
     contract.preservedStateEq s₀ s₁) ∧
    -- (2) Yet the Anneal bridge machine transitions to `.uck` because `EventLoad`
    --     violates `memaccessInbounds` (`readableRanges = []`):
    asmBridgeStep stepFn contract s₀ s₀ = .uck := by
  intro stepFn contract s₁
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine ⟨s₀.write Arm.State.PC (s₀.read Arm.State.PC + 4#64)
              |>.write Arm.State.X2 (BitVec.ofNat 64 (ByteList.toNatLE (s₀._mem.readBytesLE (s₀.read Arm.State.X1) 8))),
            ?_, ?_⟩
    · refine ⟨s₀.write Arm.State.PC (s₀.read Arm.State.PC + 4#64), ⟨s₀.read Arm.State.PC + 4#64, rfl⟩, ?_⟩
      exact ⟨s₀.write Arm.State.PC (s₀.read Arm.State.PC + 4#64)
              |>.write Arm.State.X2 (BitVec.ofNat 64 (ByteList.toNatLE (s₀._mem.readBytesLE (s₀.read Arm.State.X1) 8))),
            ⟨_, rfl⟩, rfl⟩
    · exact ⟨s₁, ⟨.EventLoad (s₀.read Arm.State.X1) 8 :: s₀.read Arm.State.events, rfl⟩, rfl⟩
  · simp [contract, s₁, stepFn, Arm.State.read, Arm.State.write, Arm.State.PC, Arm.State.X2,
      Arm.State.SP, Arm.State.events, Arm.State.XREG, Component.compose, Arm.State.regs,
      Component.element, funcUpdate]
  · have hpc' : Arm.State.PC.read s₀ = 0x1000#64 := hpc
    simp [asmBridgeStep, stepFn, contract, Arm.State.read, Arm.State.write, Arm.State.events,
      memaccessInbounds, hpc']

/-- Concrete 2-step `SafeExecutionN` + Anneal `SpecOn` refinement witness for `simple`
    (`add x2, x1, x0; sub x2, x2, x1` at `PC = 0x1000#64` exiting at `0x1008#64`):
    demonstrates that `simple` emits zero `UArchEvent`s (`memaccessInbounds [] [] [] = true`),
    satisfies `MayChange [PC, X2]`, preserves `(X19, SP, flags)`, and refines Anneal's `SpecOn`
    for `post := fun s ↦ s.read X2 = a`. -/
def simpleStepFn (s : Arm.State) : Option Arm.State :=
  if s.read Arm.State.PC == 0x1000#64 then
    some (s.write Arm.State.PC 0x1004#64
          |>.write Arm.State.X2 (s.read Arm.State.X1 + s.read Arm.State.X0))
  else if s.read Arm.State.PC == 0x1004#64 then
    some (s.write Arm.State.PC 0x1008#64
          |>.write Arm.State.X2 (s.read Arm.State.X2 - s.read Arm.State.X1))
  else
    none

def simpleBridgeContract : AnnealAsmBridgeContract where
  pcExit := 0x1008#64
  preservedStateEq a b :=
    b.read Arm.State.X19 = a.read Arm.State.X19 ∧
    b.read Arm.State.SP = a.read Arm.State.SP ∧
    b.read Arm.State.flags = a.read Arm.State.flags
  readableRanges := []
  writableRanges := []

instance : DecidableRel simpleBridgeContract.preservedStateEq :=
  fun a b ↦ by
    unfold simpleBridgeContract
    infer_instance

theorem simple_safeExecutionN_refines_anneal_specOn (s₀ : Arm.State) (a b : BitVec 64)
    (hpc : s₀.read Arm.State.PC = 0x1000#64)
    (hx0 : s₀.read Arm.State.X0 = a)
    (hx1 : s₀.read Arm.State.X1 = b) :
    ∃ bSpec,
      (asmBridgeMachine simpleStepFn simpleBridgeContract s₀).toLanguage.SpecOn
        (fun _ ↦ True) (fun s ↦ s.read Arm.State.X2 = a) () = some bSpec ∧
      (asmBridgeMachine simpleStepFn simpleBridgeContract s₀).BehaviorOf s₀ ≤ bSpec := by
  apply ensuresN_safety_refines_anneal_specOn simpleStepFn simpleBridgeContract
    (frame := Component.MayChange [Arm.State.PC, Arm.State.X2]) (n := 2)
  · intro s_end hframe
    exact Arm.simple_frame_preserves_abi_state hframe
  · let s₁ := s₀.write Arm.State.PC 0x1004#64 |>.write Arm.State.X2 (b + a)
    let s₂ := s₁.write Arm.State.PC 0x1008#64 |>.write Arm.State.X2 ((b + a) - b)
    refine SafeExecutionN.step (s' := s₁) ?_ ?_ ?_ ?_
    · rw [hpc]; decide
    · simp [simpleStepFn, hpc, hx0, hx1, s₁]
    · exact ⟨[], rfl, rfl⟩
    · refine SafeExecutionN.step (s' := s₂) ?_ ?_ ?_ ?_
      · change (0x1004#64 : BitVec 64) ≠ 0x1008#64
        decide
      · have hpc1 : s₁.read Arm.State.PC = 0x1004#64 := rfl
        have hx2_1 : s₁.read Arm.State.X2 = b + a := by
          simp [s₁, Arm.State.read, Arm.State.write, Arm.State.X2, Arm.State.PC,
            Arm.State.XREG, Component.compose, Arm.State.regs, Component.element]
        have hx1_1 : s₁.read Arm.State.X1 = b := by
          have hne12 : (1#5 : BitVec 5) ≠ 2#5 := by decide
          simpa [s₁, Arm.State.read, Arm.State.write, Arm.State.X1, Arm.State.X2, Arm.State.PC,
            Arm.State.XREG, Component.compose, Arm.State.regs, Component.element, hne12] using hx1
        simp [simpleStepFn, hpc1, hx2_1, hx1_1, s₂]
      · exact ⟨[], rfl, rfl⟩
      · refine SafeExecutionN.exit rfl ?_ ?_
        · change (b + a) - b = a
          bv_omega
        · refine ⟨s₀.write Arm.State.PC 0x1008#64, ⟨0x1008#64, rfl⟩, ?_⟩
          refine ⟨s₂, ⟨(b + a) - b, ?_⟩, rfl⟩
          simp [s₂, s₁, Component.Assign, Arm.State.write, Arm.State.PC, Arm.State.X2,
            Arm.State.XREG, Component.compose, Arm.State.regs, Component.element]

/-! ## Axiom Verification (`#guard_msgs in #print axioms`) -/

/-- info: 'CslibBignumStudy.Component.MayChange_preserves_orthogonal' does not depend on any axioms -/
#guard_msgs in
#print axioms Component.MayChange_preserves_orthogonal

/-- info: 'CslibBignumStudy.Arm.upstream_simple_stuck_at_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Arm.upstream_simple_stuck_at_entry

/-- info: 'CslibBignumStudy.Arm.simple_spec_proven' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Arm.simple_spec_proven

/-- info: 'CslibBignumStudy.Arm.simple_frame_preserves_abi_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Arm.simple_frame_preserves_abi_state

/--
info: 'CslibBignumStudy.ensuresN_safety_refines_anneal_specOn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ensuresN_safety_refines_anneal_specOn

/-- info: 'CslibBignumStudy.mayChange_alone_cannot_exclude_unauthorized_load' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mayChange_alone_cannot_exclude_unauthorized_load

/--
info: 'CslibBignumStudy.simple_safeExecutionN_refines_anneal_specOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms simple_safeExecutionN_refines_anneal_specOn

end CslibBignumStudy
