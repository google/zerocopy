/-
  support/kraken_wp_and_bridge_probe.lean

  Self-contained Lean 4.34.1 mechanization for:
    `kraken-wp-foundation-directive-refactor-and-syntax-elaborators-c9aa45e`

  This file mechanizes and verifies:
  1. Kraken's abstracted `Directive Instr`, `Executable Instr`, and `Layout Instr`
     introduced in PR #211 (`46e5fe90770d3e0e81313c357512dfd929ffb641` / `c9aa45ee1b273892d7efa7bbf8a8a9391e17b2c0`).
  2. Kraken's `Host` typeclass (`zero_inert`, `addr_determines_offset`), `Directive.Inert`,
     `List.IsInfixAt`, and `Program.wp` weakest-precondition foundation over `Eventually (step1 Host.exe)`
     introduced in PR #165 (`1b5c3e47bc8f2b75c6575be7f00904ea63d99bdd`, `188cb1e8cf3802041b5732e8632252aa16a1192f`).
  3. The permission-erasure gap in `Effects.All` (which still ignores `require_read_access`,
     `require_write_access`, and `require_exec_access` at `c9aa45ee1`), the `Directive.Inert`
     subtlety for zero-sized instructions vs. labels, and the persistent `loadAvx`/`storeAvx`
     `.W64` (8-byte) access-width bug for 16/32/64-byte AVX accesses.
  4. A strict permission-enforcing observer `Effects.StrictAll` and strict weakest precondition
     `Program.wpStrict`, bridged via `BridgeEffects` into Anneal's Layer 1B (`StepResult`,
     `SmallStepMachine`, `BehaviorOf`) and Layer 1A (`Partial`, `SpecOn`, `WellFormedOn`),
     with both positive refinement theorems and negative controls.
-/

namespace KrakenWPAndBridgeProbe

/-! ## Section 1: Abstracted `Directive Instr`, `Executable Instr`, and `Layout Instr` (PR #211) -/

abbrev Label := String

/-- Width of scalar memory accesses in bytes. -/
inductive Width where
  | W8 | W16 | W32 | W64
  deriving DecidableEq, Repr

def Width.bytes : Width → Nat
  | .W8  => 1
  | .W16 => 2
  | .W32 => 4
  | .W64 => 8

/-- Width of AVX vector memory accesses in bytes. -/
inductive AvxWidth where
  | W128 | W256 | W512
  deriving DecidableEq, Repr

def AvxWidth.bytes : AvxWidth → Nat
  | .W128 => 16
  | .W256 => 32
  | .W512 => 64

/-- Architecture-parametric assembly directive (`Kraken/Layout.lean:19-23` at `c9aa45ee1`). -/
inductive Directive (Instr : Type) where
  | instr (_ : Instr)
  | label (_ : Label)
  | byteArray (_ : List UInt8)
  deriving DecidableEq, Repr

abbrev Program (Instr : Type) := List (Directive Instr)

structure Sized (α : Type) where
  directive : α
  size : Nat
  deriving DecidableEq, Repr

structure AddressRange where
  addr : Nat
  size : Nat
  deriving DecidableEq, Repr

def AddressRange.upper (r : AddressRange) : Nat :=
  r.addr + r.size

structure Addressable (α : Type) extends AddressRange where
  directive : α
  deriving DecidableEq, Repr

/-- Architecture-parametric laid-out executable (`Kraken/Layout.lean:34-36` at `c9aa45ee1`). -/
structure Executable (Instr : Type) where
  program : List (Sized (Directive Instr))
  deriving DecidableEq, Repr

/-- Architecture-parametric layout (`Kraken/Layout.lean:38-53` at `c9aa45ee1`). -/
class Layout (Instr : Type) where
  size : Nat → Nat

def Layout.apply {Instr : Type} (l : Layout Instr) (p : Program Instr) : Executable Instr :=
  ⟨p.zipIdx.map fun (d, i) =>
    match d with
    | .instr _ => ⟨d, @Layout.size Instr l i⟩
    | .label _ => ⟨d, 0⟩
    | .byteArray arr => ⟨d, arr.length⟩⟩

/-- Uses `List (Directive Instr)` explicitly so `CoeFun` synthesis succeeds on architecture
    `Program` abbreviations (`Kraken/Layout.lean:51-52`). -/
instance {Instr : Type} : CoeFun (Layout Instr) (fun _ => List (Directive Instr) → Executable Instr) :=
  ⟨Layout.apply⟩

class Labels where
  label : Label → Int

def Executable.withAddressesAux {Instr : Type} (addr : Nat) :
    List (Sized (Directive Instr)) → List (Addressable (Directive Instr))
  | [] => []
  | ⟨d, sz⟩ :: rest =>
    ⟨⟨addr, sz⟩, d⟩ :: Executable.withAddressesAux (addr + sz) rest

def Executable.withAddresses {Instr : Type} (e : Executable Instr) :
    List (Addressable (Directive Instr)) :=
  Executable.withAddressesAux 0 e.program

def Executable.directivesAtAddress {Instr : Type} (e : Executable Instr) (pc : Nat) :
    List (Addressable (Directive Instr)) :=
  let suffix := e.withAddresses.dropWhile (fun d => decide (d.addr ≠ pc))
  match suffix.findIdx? (fun d => decide (0 < d.size)) with
  | some k => suffix.take (k + 1)
  | none => suffix.takeWhile (fun d => decide (d.addr = pc))

def Executable.sizeBefore {Instr : Type} (e : Executable Instr) (k : Nat) : Nat :=
  ((e.program.take k).map Sized.size).sum

def Executable.addrOf {Instr : Type} (e : Executable Instr) (k : Nat) : Nat :=
  e.sizeBefore k

/-! ## Section 2: `List.IsInfixAt`, `Effects`, `OmniSemantics`, and `Directive.Inert` -/

/-- `l₁` occurs in `l₂` starting at index `k` (`Kraken/Data/List/Infix.lean:24-25`). -/
def List.IsInfixAt {α : Type} (l₁ l₂ : List α) (k : Nat) : Prop :=
  l₁ <+: l₂.drop k

theorem List.IsInfixAt.nil {α : Type} (l : List α) (k : Nat) :
    List.IsInfixAt [] l k :=
  List.nil_prefix

theorem List.IsInfixAt.cons_iff {α : Type} {x : α} {xs l : List α} {k : Nat} :
    List.IsInfixAt (x :: xs) l k ↔ l[k]? = some x ∧ List.IsInfixAt xs l (k + 1) := by
  unfold List.IsInfixAt
  cases h : l.drop k with
  | nil =>
    have hget : l[k]? = none := by
      rw [← List.head?_drop, h]
      rfl
    simp [hget]
  | cons y ys =>
    have hget : l[k]? = some y := by
      rw [← List.head?_drop, h]
      rfl
    have hdrop : l.drop (k + 1) = ys := by
      rw [← List.drop_drop, h]
      rfl
    rw [hget, hdrop]
    simp only [List.cons_prefix_cons, Option.some.injEq]
    exact ⟨fun ⟨hxy, hxs⟩ => ⟨hxy.symm, hxs⟩, fun ⟨hyx, hxs⟩ => ⟨hyx.symm, hxs⟩⟩

/-- Interaction-tree `Effects` datatype (`Kraken/X64/Semantics.lean` and `Kraken/AArch64/Semantics.lean`). -/
inductive Effects (State : Type) where
  | done (s : State)
  | undefined (T : Type) (defaultVal : T) (cont : T → Effects State)
  | unimplemented (msg : String)
  | gp_unaligned (addr : Nat)
  | nonmem_load (addr : Nat) (w : Width)
  | nonmem_store (addr : Nat) (w : Width)
  | require_read_access (addr : Nat) (w : Width) (cont : Unit → Effects State)
  | require_write_access (addr : Nat) (w : Width) (cont : Unit → Effects State)
  | require_exec_access (range : AddressRange) (cont : Unit → Effects State)

/-- Kraken's default omni-semantics observer (`Kraken/X64/OmniSemantics.lean:13-22` at `c9aa45ee1`).
    Notice that `require_read_access`, `require_write_access`, and `require_exec_access`
    unconditionally ignore their address/width/range parameters! -/
def Effects.All {State : Type} (e : Effects State) (post : State → Prop) : Prop :=
  match e with
  | .done s => post s
  | .undefined T _ cont => ∀ v : T, (cont v).All post
  | .unimplemented _ => False
  | .gp_unaligned _ => False
  | .nonmem_load _ _ => False
  | .nonmem_store _ _ => False
  | .require_read_access _ _ cont => (cont ()).All post
  | .require_write_access _ _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

theorem Effects.All.mono {State : Type} {e : Effects State} {P Q : State → Prop}
    (hPQ : ∀ s, P s → Q s) (he : e.All P) : e.All Q := by
  induction e with
  | done s => exact hPQ s he
  | undefined T _ cont ih =>
    intro v
    exact ih v (he v)
  | unimplemented _ => exact False.elim he
  | gp_unaligned _ => exact False.elim he
  | nonmem_load _ _ => exact False.elim he
  | nonmem_store _ _ => exact False.elim he
  | require_read_access _ _ cont ih => exact ih () he
  | require_write_access _ _ cont ih => exact ih () he
  | require_exec_access _ cont ih => exact ih () he

/-- Inductive `Eventually` fixpoint (`Kraken/OmniSemantics.lean:25-30`). -/
inductive Eventually {State : Type} (step : State → (State → Prop) → Prop)
    (P : State → Prop) : State → Prop where
  | now {s} : P s → Eventually step P s
  | step {s Q} : step s Q → (∀ s', Q s' → Eventually step P s') → Eventually step P s

theorem Eventually.mono {State : Type} {step : State → (State → Prop) → Prop}
    {P Q : State → Prop} (hPQ : ∀ s, P s → Q s) {s : State}
    (h : Eventually step P s) : Eventually step Q s := by
  induction h with
  | now hp => exact .now (hPQ _ hp)
  | step hs _ ih => exact .step hs ih

theorem Eventually.trans {State : Type} {step : State → (State → Prop) → Prop}
    {P Q : State → Prop} {s : State}
    (h1 : Eventually step P s) (h2 : ∀ s', P s' → Eventually step Q s') :
    Eventually step Q s := by
  induction h1 with
  | now hp => exact h2 _ hp
  | step hs _ ih => exact .step hs ih

/-! ## Section 3: Concrete Model of X64 `Instr`, `Directive.interp`, `Host`, and `Program.wp` -/

structure MachineData where
  reg0 : UInt64
  mem0 : Nat → Option UInt64

structure MachineState where
  data : MachineData
  pc : Nat

/-- Representative instruction set capturing scalar load/store, zero-sized/sized nop,
    and AVX 256-bit load (modeling `Kraken/X64/Semantics.lean`). -/
inductive Instr where
  | nop (sz : Nat)
  | store64 (addr : Nat) (val : UInt64)
  | load64 (addr : Nat)
  | vmovupsLoad256 (addr : Nat)
  deriving DecidableEq, Repr

/-- Faithful model of `MachineData.loadAvx` (`Kraken/X64/Semantics.lean:317-326` at `c9aa45ee1`):
    emits `require_read_access addr .W64` (8 bytes) even when reading `.W256` (32 bytes)! -/
def loadAvxBuggy (s : MachineData) (addr : Nat) (w : AvxWidth)
    (cont : UInt64 → Effects MachineState) : Effects MachineState :=
  .require_read_access addr .W64 fun () =>
    let numWords := w.bytes / 8
    if (List.range numWords).all (fun i => (s.mem0 (addr + 8 * i)).isSome) then
      match s.mem0 addr with
      | some v => cont v
      | none => .nonmem_load addr .W64
    else
      .nonmem_load addr .W64

def Instr.interp (i : Instr) (s : MachineData) (p : AddressRange)
    (next : MachineData → Effects MachineState) : Effects MachineState :=
  .require_exec_access p fun () =>
    match i with
    | .nop _ => next s
    | .store64 addr val =>
      .require_write_access addr .W64 fun () =>
        match s.mem0 addr with
        | some _ =>
          next { s with mem0 := fun a => if a = addr then some val else s.mem0 a }
        | none => .nonmem_store addr .W64
    | .load64 addr =>
      .require_read_access addr .W64 fun () =>
        match s.mem0 addr with
        | some v => next { s with reg0 := v }
        | none => .nonmem_load addr .W64
    | .vmovupsLoad256 addr =>
      loadAvxBuggy s addr .W256 fun v =>
        next { s with reg0 := v }

/-- `Directive.interp` (`Kraken/X64/Semantics.lean:805-808` and `Kraken/AArch64/Semantics.lean:962-965`). -/
def Directive.interp (d : Directive Instr) (s : MachineData) (p : AddressRange)
    (next : MachineData → Effects MachineState) : Effects MachineState :=
  match d with
  | .instr i => i.interp s p next
  | .label _ => next s
  | .byteArray _ => .unimplemented "Unimplemented: execution reached data block"

def Directives.interp (ds : List (Addressable (Directive Instr))) (s : MachineData)
    (next : MachineData → Effects MachineState) : Effects MachineState :=
  match ds with
  | [] => next s
  | d :: rest =>
    d.directive.interp s d.toAddressRange (fun s' => Directives.interp rest s' next)

/-- `Directive.Inert` (`Kraken/X64/Inert.lean:13-15` at `c9aa45ee1`). -/
def Directive.Inert (d : Directive Instr) : Prop :=
  ∀ s p next post, (d.interp s p next).All post ↔ (next s).All post

theorem Directive.Inert.label (l : Label) : Directive.Inert (.label l) := by
  intro s p next post
  rfl

theorem Directive.Inert.nop (sz : Nat) : Directive.Inert (.instr (.nop sz)) := by
  intro s p next post
  rfl

theorem Directives.interp_inert_append (pre : List (Addressable (Directive Instr)))
    (hpre : ∀ d ∈ pre, d.directive.Inert)
    (ds : List (Addressable (Directive Instr)))
    (s : MachineData) (next : MachineData → Effects MachineState) (post : MachineState → Prop) :
    (Directives.interp (pre ++ ds) s next).All post ↔ (Directives.interp ds s next).All post := by
  induction pre generalizing s with
  | nil => rfl
  | cons d rest ih =>
    have hd : d.directive.Inert := hpre d (.head _)
    have hrest : ∀ d' ∈ rest, d'.directive.Inert := fun d' hm => hpre d' (.tail _ hm)
    simp only [List.cons_append, Directives.interp]
    rw [hd]
    exact ih hrest s

/-- Single-step omni-semantics relation `step1` (`Kraken/X64/OmniSemantics.lean:24-28`). -/
def step1 (e : Executable Instr) (st : MachineState) (post : MachineState → Prop) : Prop :=
  match e.directivesAtAddress st.pc with
  | [] => False
  | d :: rest =>
    let lastRange := ((d :: rest).getLast (List.cons_ne_nil d rest)).toAddressRange
    (Directives.interp (d :: rest) st.data (fun s' => .done ⟨s', lastRange.upper⟩)).All post

/-- `Host` typeclass (`Kraken/X64/WP/Host.lean:25-33` at `c9aa45ee1`). -/
class Host where
  prog : Program Instr
  layout : Layout Instr
  zero_inert : ∀ i d, prog[i]? = some d → @Layout.size Instr layout i = 0 → d.Inert
  addr_determines_offset :
    ∀ j k, (layout.apply prog).addrOf j = (layout.apply prog).addrOf k →
      (layout.apply prog).sizeBefore j = (layout.apply prog).sizeBefore k

def Host.exe [h : Host] : Executable Instr :=
  h.layout.apply h.prog

def Host.addrOf [Host] (k : Nat) : Nat :=
  Host.exe.addrOf k

/-- `Program.wp` (`Kraken/X64/WP/Basic.lean:27-33` at `c9aa45ee1`). -/
def Program.wp [Host] (p : Program Instr) (Q : MachineData → Prop)
    (E : Nat → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ k, List.IsInfixAt p Host.prog k →
    Eventually (step1 Host.exe)
      (fun st => (st.pc = Host.addrOf (k + p.length) ∧ Q st.data) ∨ E st.pc st.data)
      ⟨s, Host.addrOf k⟩

theorem Program.wp_mono [Host] {p : Program Instr}
    {Q Q' : MachineData → Prop} {E E' : Nat → MachineData → Prop} {s : MachineData}
    (hQ : ∀ d, Q d → Q' d) (hE : ∀ pc d, E pc d → E' pc d)
    (hwp : Program.wp p Q E s) : Program.wp p Q' E' s := by
  intro k hk
  refine (hwp k hk).mono ?_
  intro st hst
  rcases hst with ⟨hpc, hq⟩ | he
  · exact Or.inl ⟨hpc, hQ st.data hq⟩
  · exact Or.inr (hE st.pc st.data he)

theorem Program.wp_nil [Host] {Q : MachineData → Prop} {E : Nat → MachineData → Prop}
    {s : MachineData} (hs : Q s) : Program.wp [] Q E s := by
  intro k _
  exact .now (Or.inl ⟨by simp, hs⟩)

/-- Compositional sequencing rule (`Program.wp_cons`, `Kraken/X64/WP/Basic.lean:40-53`). -/
theorem Program.wp_cons [Host] {d : Directive Instr} {p : Program Instr}
    {Q R : MachineData → Prop} {E : Nat → MachineData → Prop} {s : MachineData}
    (hd : Program.wp [d] Q E s)
    (hp : ∀ s', Q s' → Program.wp p R E s') :
    Program.wp (d :: p) R E s := by
  intro k hk
  rw [List.IsInfixAt.cons_iff] at hk
  rcases hk with ⟨hdk, hpk⟩
  have hd_at : List.IsInfixAt [d] Host.prog k := by
    rw [List.IsInfixAt.cons_iff]
    exact ⟨hdk, List.IsInfixAt.nil _ _⟩
  refine (hd k hd_at).trans ?_
  intro st hst
  rcases hst with ⟨hpc, hq⟩ | he
  · have hstep := hp st.data hq (k + 1) hpk
    cases st with
    | mk data pc =>
      simp only at hpc hq
      rw [hpc]
      refine hstep.mono ?_
      intro st' hst'
      rcases hst' with ⟨hpc', hr⟩ | he'
      · exact Or.inl ⟨by rw [hpc']; simp [Nat.add_right_comm, Nat.add_assoc], hr⟩
      · exact Or.inr he'
  · exact .now (Or.inr he)

/-- Core single-directive adequacy lemma (`Host.eventually_of_interp`,
    `Kraken/X64/WP/Basic.lean:58-77`): when `directivesAtAddress (addrOf k)` decomposes into
    an inert prefix `pre` followed by the positive-sized directive `c` (`Host.directivesAtAddress_addrOf`,
    `Kraken/X64/WP/Host.lean:77-105`), proving `(c.directive.interp ...).All post` immediately
    yields `step1 Host.exe ⟨s, Host.addrOf k⟩ post` and `Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩`. -/
theorem Directives.interp_snoc (pre : List (Addressable (Directive Instr)))
    (c : Addressable (Directive Instr)) (s : MachineData)
    (next : MachineData → Effects MachineState) :
    Directives.interp (pre ++ [c]) s next =
      Directives.interp pre s (fun s' => c.directive.interp s' c.toAddressRange next) := by
  induction pre generalizing s with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.cons_append, Directives.interp]
    congr 1
    funext s'
    exact ih s'

theorem Host.step1_of_interp_decomp [Host] {k : Nat}
    {pre : List (Addressable (Directive Instr))} {c : Addressable (Directive Instr)}
    (hdir : Host.exe.directivesAtAddress (Host.addrOf k) = pre ++ [c])
    (hinert : ∀ d ∈ pre, d.directive.Inert)
    {s : MachineData} {post : MachineState → Prop}
    (hinterp : (c.directive.interp s c.toAddressRange
      (fun s' => .done ⟨s', c.toAddressRange.upper⟩)).All post) :
    step1 Host.exe ⟨s, Host.addrOf k⟩ post := by
  unfold step1
  dsimp only
  cases hds : Host.exe.directivesAtAddress (Host.addrOf k) with
  | nil =>
    rw [hdir] at hds
    exact False.elim (List.cons_ne_nil c [] (List.append_eq_nil_iff.mp hds).2)
  | cons d rest =>
    dsimp only
    have heq : d :: rest = pre ++ [c] := by rw [← hds, hdir]
    have hlast : (d :: rest).getLast (List.cons_ne_nil d rest) = c := by
      have hne : pre ++ [c] ≠ [] := by
        intro h
        exact List.cons_ne_nil c [] (List.append_eq_nil_iff.mp h).2
      have hget : (d :: rest).getLast (List.cons_ne_nil d rest) = (pre ++ [c]).getLast hne := by
        congr 1
      rw [hget, List.getLast_append_of_ne_nil _ (List.cons_ne_nil c [])]
      rfl
    rw [hlast, heq]
    exact (Directives.interp_inert_append pre hinert [c] s
      (fun s' => .done ⟨s', c.toAddressRange.upper⟩) post).mpr hinterp

theorem Host.eventually_of_interp_decomp [Host] {k : Nat}
    {pre : List (Addressable (Directive Instr))} {c : Addressable (Directive Instr)}
    (hdir : Host.exe.directivesAtAddress (Host.addrOf k) = pre ++ [c])
    (hinert : ∀ d ∈ pre, d.directive.Inert)
    {s : MachineData} {post : MachineState → Prop}
    (hinterp : (c.directive.interp s c.toAddressRange
      (fun s' => .done ⟨s', c.toAddressRange.upper⟩)).All post) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ :=
  .step (Host.step1_of_interp_decomp hdir hinert hinterp) (fun _ h => .now h)

/-- Adequacy bridge from `Program.wp` at a concrete index `k` to `Eventually (step1 Host.exe)`
    (`Program.step1_of_wp_at`, `Kraken/X64/WP/Basic.lean:87-96`). -/
theorem Program.step1_of_wp_at [Host] {p : Program Instr}
    {Q : MachineData → Prop} {E : Nat → MachineData → Prop} {s : MachineData}
    {k : Nat} (hk : List.IsInfixAt p Host.prog k)
    (hwp : Program.wp p Q E s)
    {post : MachineState → Prop}
    (hpost : ∀ st, ((st.pc = Host.addrOf (k + p.length) ∧ Q st.data) ∨ E st.pc st.data) → post st) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ :=
  (hwp k hk).mono hpost

/-! ## Section 4: Strict Permission Observer `Effects.StrictAll` and `Program.wpStrict` -/

/-- Explicit architectural permission policy over `[addr, addr + bytes)`. -/
structure PermPolicy where
  canRead : Nat → Nat → Bool
  canWrite : Nat → Nat → Bool
  canExec : AddressRange → Bool

/-- Strict omni-semantics observer that enforces `require_read_access`, `require_write_access`,
    and `require_exec_access` against `perm : PermPolicy` rather than erasing them. -/
def Effects.StrictAll {State : Type} (perm : PermPolicy) (e : Effects State)
    (post : State → Prop) : Prop :=
  match e with
  | .done s => post s
  | .undefined T _ cont => ∀ v : T, (cont v).StrictAll perm post
  | .unimplemented _ => False
  | .gp_unaligned _ => False
  | .nonmem_load _ _ => False
  | .nonmem_store _ _ => False
  | .require_read_access addr w cont =>
    perm.canRead addr w.bytes = true ∧ (cont ()).StrictAll perm post
  | .require_write_access addr w cont =>
    perm.canWrite addr w.bytes = true ∧ (cont ()).StrictAll perm post
  | .require_exec_access range cont =>
    perm.canExec range = true ∧ (cont ()).StrictAll perm post

theorem Effects.StrictAll.mono {State : Type} {perm : PermPolicy} {e : Effects State}
    {P Q : State → Prop} (hPQ : ∀ s, P s → Q s) (he : e.StrictAll perm P) :
    e.StrictAll perm Q := by
  induction e with
  | done s => exact hPQ s he
  | undefined T _ cont ih =>
    intro v
    exact ih v (he v)
  | unimplemented _ => exact False.elim he
  | gp_unaligned _ => exact False.elim he
  | nonmem_load _ _ => exact False.elim he
  | nonmem_store _ _ => exact False.elim he
  | require_read_access _ _ cont ih => exact ⟨he.1, ih () he.2⟩
  | require_write_access _ _ cont ih => exact ⟨he.1, ih () he.2⟩
  | require_exec_access _ cont ih => exact ⟨he.1, ih () he.2⟩

/-- Soundness of `StrictAll` wrt `Effects.All`: every strict proof implies Kraken's `Effects.All`. -/
theorem Effects.StrictAll.toAll {State : Type} {perm : PermPolicy} {e : Effects State}
    {post : State → Prop} (he : e.StrictAll perm post) : e.All post := by
  induction e with
  | done s => exact he
  | undefined T _ cont ih =>
    intro v
    exact ih v (he v)
  | unimplemented _ => exact False.elim he
  | gp_unaligned _ => exact False.elim he
  | nonmem_load _ _ => exact False.elim he
  | nonmem_store _ _ => exact False.elim he
  | require_read_access _ _ cont ih => exact ih () he.2
  | require_write_access _ _ cont ih => exact ih () he.2
  | require_exec_access _ cont ih => exact ih () he.2

/-- Subtlety in `Directive.Inert`:
    1. `.label l` is unconditionally inert under `StrictAll perm` for *every* `perm`.
    2. `.instr (.nop 0)` is inert under `Effects.All`, but under `StrictAll perm` it requires
       `perm.canExec p = true`! -/
theorem label_strict_inert (perm : PermPolicy) (l : Label)
    (s : MachineData) (p : AddressRange) (next : MachineData → Effects MachineState)
    (post : MachineState → Prop) :
    (Directive.interp (.label l) s p next).StrictAll perm post ↔ (next s).StrictAll perm post := by
  rfl

theorem nop0_not_strict_inert_when_unexec :
    let perm : PermPolicy := {
      canRead := fun _ _ => true
      canWrite := fun _ _ => true
      canExec := fun _ => false
    }
    let s : MachineData := { reg0 := 0, mem0 := fun _ => some 0 }
    let p : AddressRange := { addr := 0, size := 0 }
    let next : MachineData → Effects MachineState := fun s' => .done ⟨s', 0⟩
    (Directive.interp (.instr (.nop 0)) s p next).All (fun _ => True) ∧
    ¬ (Directive.interp (.instr (.nop 0)) s p next).StrictAll perm (fun _ => True) := by
  refine ⟨trivial, ?_⟩
  intro h
  exact Bool.noConfusion h.1

/-- Demonstration of the `loadAvx` `.W64` access-width mismatch (`Kraken/X64/Semantics.lean:318`):
    When only `[0x1000, 0x1008)` (8 bytes) has read permission in `perm`, while the underlying
    `MachineData.mem0` is mapped across `[0x1000, 0x1020)`, `vmovupsLoad256 0x1000` (which reads
    32 bytes) erroneously satisfies `StrictAll perm` because `loadAvx` emits
    `require_read_access 0x1000 .W64` (8 bytes) instead of 32 bytes! -/
def permOnly8BytesAt0x1000 : PermPolicy where
  canRead := fun addr bytes => decide (addr = 0x1000 ∧ bytes ≤ 8)
  canWrite := fun _ _ => false
  canExec := fun _ => true

def mapped32BytesState : MachineData where
  reg0 := 0
  mem0 := fun a =>
    if a = 0x1000 ∨ a = 0x1008 ∨ a = 0x1010 ∨ a = 0x1018 then some 99 else none

theorem vmovupsLoad256_passes_buggy_W64_perm_check :
    (Instr.interp (.vmovupsLoad256 0x1000) mapped32BytesState ⟨0, 4⟩
      (fun s' => .done ⟨s', 4⟩)).StrictAll permOnly8BytesAt0x1000 (fun st => st.data.reg0 = 99) := by
  refine ⟨rfl, rfl, ?_⟩
  rfl

/-- Corrected AVX load helper that checks the full `w.bytes` (32 bytes for `W256`). -/
def checkAvxReadPerm (perm : PermPolicy) (addr : Nat) (w : AvxWidth) : Bool :=
  perm.canRead addr w.bytes

theorem vmovupsLoad256_rejected_by_true_W256_width_check :
    checkAvxReadPerm permOnly8BytesAt0x1000 0x1000 .W256 = false := by
  rfl

/-- Strict single-step relation `step1Strict` enforcing `perm : PermPolicy`. -/
def step1Strict (perm : PermPolicy) (e : Executable Instr) (st : MachineState)
    (post : MachineState → Prop) : Prop :=
  match e.directivesAtAddress st.pc with
  | [] => False
  | d :: rest =>
    let lastRange := ((d :: rest).getLast (List.cons_ne_nil d rest)).toAddressRange
    (Directives.interp (d :: rest) st.data (fun s' => .done ⟨s', lastRange.upper⟩)).StrictAll perm post

/-- Strict weakest precondition `Program.wpStrict`. -/
def Program.wpStrict [Host] (perm : PermPolicy) (p : Program Instr)
    (Q : MachineData → Prop) (E : Nat → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ k, List.IsInfixAt p Host.prog k →
    Eventually (step1Strict perm Host.exe)
      (fun st => (st.pc = Host.addrOf (k + p.length) ∧ Q st.data) ∨ E st.pc st.data)
      ⟨s, Host.addrOf k⟩

theorem step1Strict_to_step1 {perm : PermPolicy} {e : Executable Instr}
    {st : MachineState} {post : MachineState → Prop}
    (h : step1Strict perm e st post) : step1 e st post := by
  unfold step1Strict at h
  unfold step1
  split at h
  · exact h
  · exact h.toAll

theorem Eventually.of_step1Strict {perm : PermPolicy} {e : Executable Instr}
    {P : MachineState → Prop} {st : MachineState}
    (h : Eventually (step1Strict perm e) P st) : Eventually (step1 e) P st := by
  induction h with
  | now hp => exact .now hp
  | step hs _ ih => exact .step (step1Strict_to_step1 hs) ih

theorem Program.wpStrict_to_wp [Host] {perm : PermPolicy} {p : Program Instr}
    {Q : MachineData → Prop} {E : Nat → MachineData → Prop} {s : MachineData}
    (h : Program.wpStrict perm p Q E s) : Program.wp p Q E s := by
  intro k hk
  exact Eventually.of_step1Strict (h k hk)

/-! ## Section 5: Anneal Layer 1A (`Refinement`) & Layer 1B (`StepResult`) Mechanization -/

/-- Anneal Layer 1A `Preorder` (`trusted/lean/Trusted/Refinement.lean:15-21`). -/
class Preorder (α : Type) extends LE α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c

/-- Anneal Layer 1A `Partial` (`trusted/lean/Trusted/Refinement.lean:47-49`). -/
structure Partial (Out : Type) where
  defined : Prop
  val : defined → (Out → Prop)

instance {Out : Type} : LE (Partial Out) where
  le b₁ b₂ := ∀ h₂ : b₂.defined, ∃ h₁ : b₁.defined, ∀ o, b₁.val h₁ o → b₂.val h₂ o

instance {Out : Type} : Preorder (Partial Out) where
  le_refl _ := fun h => ⟨h, fun _ ho => ho⟩
  le_trans h12 h23 := fun h3 =>
    let ⟨h2, hsub23⟩ := h23 h3
    let ⟨h1, hsub12⟩ := h12 h2
    ⟨h1, fun o ho => hsub23 o (hsub12 o ho)⟩

def Behavior (In Out : Type) : Type :=
  In → Partial Out

instance {In Out : Type} : LE (Behavior In Out) where
  le f g := ∀ i, f i ≤ g i

instance {In Out : Type} : Preorder (Behavior In Out) where
  le_refl f i := Preorder.le_refl (f i)
  le_trans h12 h23 i := Preorder.le_trans (h12 i) (h23 i)

structure Language where
  Prog : Type
  In : Type
  Out : Type
  exec : Prog → Behavior In Out

def Language.SpecOn (L : Language) (pre : L.In → Prop) (Post : L.In → L.Out → Prop) :
    Behavior L.In L.Out :=
  fun i => {
    defined := pre i
    val := fun _ o => Post i o
  }

def Language.WellFormedOn (L : Language) (pre : L.In → Prop) : Behavior L.In L.Out :=
  L.SpecOn pre (fun _ _ => True)

/-- Anneal Layer 1B `FailureKind`, `StepResult`, `PrefixOutcome`, and `SmallStepMachine`
    (`trusted/lean/Trusted/StepResult.lean:25-115`). -/
inductive FailureKind where
  | ub
  | incomplete
  deriving DecidableEq, Repr

inductive StepResult (State Obs : Type) where
  | next (s' : State) (o : Option Obs)
  | halted
  | failed (k : FailureKind)
  deriving DecidableEq, Repr

structure ExecQuery (State : Type) where
  init : State
  steps : Nat

inductive PrefixOutcome (State : Type) where
  | running (s : State)
  | halted (s : State)
  | failed (k : FailureKind)
  deriving DecidableEq, Repr

def PrefixOutcome.isSafe {State : Type} : PrefixOutcome State → Prop
  | .running _ => True
  | .halted _ => True
  | .failed _ => False

structure SmallStepMachine where
  Prog : Type
  State : Type
  Obs : Type
  step : Prog → State → StepResult State Obs → Prop
  step_nonempty : ∀ p s, ∃ r, step p s r

inductive ReachesPrefix (M : SmallStepMachine) (p : M.Prog) :
    Nat → M.State → List M.Obs → PrefixOutcome M.State → Prop where
  | zero (s : M.State) :
    ReachesPrefix M p 0 s [] (.running s)
  | step_next {n : Nat} {s s' : M.State} {tr : List M.Obs} {out : PrefixOutcome M.State} :
    M.step p s (.next s' none) →
    ReachesPrefix M p n s' tr out →
    ReachesPrefix M p (n + 1) s tr out
  | step_halted {n : Nat} {s : M.State} :
    M.step p s .halted →
    ReachesPrefix M p (n + 1) s [] (.halted s)
  | step_failed {n : Nat} {s : M.State} {k : FailureKind} :
    M.step p s (.failed k) →
    ReachesPrefix M p (n + 1) s [] (.failed k)

def BehaviorOf (M : SmallStepMachine) (p : M.Prog) :
    Behavior (ExecQuery M.State) (List M.Obs × PrefixOutcome M.State) :=
  fun q => {
    defined := ∀ tr out, ReachesPrefix M p q.steps q.init tr out → out.isSafe
    val := fun _ pair => ReachesPrefix M p q.steps q.init pair.1 pair.2
  }

def SmallStepMachine.toLanguage (M : SmallStepMachine) : Language where
  Prog := M.Prog
  In := ExecQuery M.State
  Out := List M.Obs × PrefixOutcome M.State
  exec := BehaviorOf M

/-! ## Section 6: Bridging `Effects` / `Program.wpStrict` to Anneal's `SmallStepMachine` -/

/-- Bridges a single Kraken `Effects MachineState` tree (under a strict permission policy `perm`)
    into Anneal's `StepResult MachineState Unit`. -/
inductive BridgeEffects (perm : PermPolicy) :
    Effects MachineState → StepResult MachineState Unit → Prop where
  | done (st : MachineState) :
    BridgeEffects perm (.done st) (.next st none)
  | undefined {T : Type} {defaultVal : T} {cont : T → Effects MachineState}
      (v : T) {r : StepResult MachineState Unit} :
    BridgeEffects perm (cont v) r →
    BridgeEffects perm (.undefined T defaultVal cont) r
  | unimplemented (msg : String) :
    BridgeEffects perm (.unimplemented msg) (.failed .incomplete)
  | gp_unaligned (addr : Nat) :
    BridgeEffects perm (.gp_unaligned addr) (.failed .ub)
  | nonmem_load (addr : Nat) (w : Width) :
    BridgeEffects perm (.nonmem_load addr w) (.failed .ub)
  | nonmem_store (addr : Nat) (w : Width) :
    BridgeEffects perm (.nonmem_store addr w) (.failed .ub)
  | read_ok {addr : Nat} {w : Width} {cont : Unit → Effects MachineState}
      {r : StepResult MachineState Unit} :
    perm.canRead addr w.bytes = true →
    BridgeEffects perm (cont ()) r →
    BridgeEffects perm (.require_read_access addr w cont) r
  | read_fail {addr : Nat} {w : Width} {cont : Unit → Effects MachineState} :
    perm.canRead addr w.bytes = false →
    BridgeEffects perm (.require_read_access addr w cont) (.failed .ub)
  | write_ok {addr : Nat} {w : Width} {cont : Unit → Effects MachineState}
      {r : StepResult MachineState Unit} :
    perm.canWrite addr w.bytes = true →
    BridgeEffects perm (cont ()) r →
    BridgeEffects perm (.require_write_access addr w cont) r
  | write_fail {addr : Nat} {w : Width} {cont : Unit → Effects MachineState} :
    perm.canWrite addr w.bytes = false →
    BridgeEffects perm (.require_write_access addr w cont) (.failed .ub)
  | exec_ok {range : AddressRange} {cont : Unit → Effects MachineState}
      {r : StepResult MachineState Unit} :
    perm.canExec range = true →
    BridgeEffects perm (cont ()) r →
    BridgeEffects perm (.require_exec_access range cont) r
  | exec_fail {range : AddressRange} {cont : Unit → Effects MachineState} :
    perm.canExec range = false →
    BridgeEffects perm (.require_exec_access range cont) (.failed .ub)

theorem BridgeEffects.nonempty (perm : PermPolicy) (e : Effects MachineState) :
    ∃ r, BridgeEffects perm e r := by
  induction e with
  | done st => exact ⟨.next st none, .done st⟩
  | undefined T defaultVal cont ih =>
    rcases ih defaultVal with ⟨r, hr⟩
    exact ⟨r, .undefined defaultVal hr⟩
  | unimplemented msg => exact ⟨.failed .incomplete, .unimplemented msg⟩
  | gp_unaligned addr => exact ⟨.failed .ub, .gp_unaligned addr⟩
  | nonmem_load addr w => exact ⟨.failed .ub, .nonmem_load addr w⟩
  | nonmem_store addr w => exact ⟨.failed .ub, .nonmem_store addr w⟩
  | require_read_access addr w cont ih =>
    cases h : perm.canRead addr w.bytes
    · exact ⟨.failed .ub, .read_fail h⟩
    · rcases ih () with ⟨r, hr⟩
      exact ⟨r, .read_ok h hr⟩
  | require_write_access addr w cont ih =>
    cases h : perm.canWrite addr w.bytes
    · exact ⟨.failed .ub, .write_fail h⟩
    · rcases ih () with ⟨r, hr⟩
      exact ⟨r, .write_ok h hr⟩
  | require_exec_access range cont ih =>
    cases h : perm.canExec range
    · exact ⟨.failed .ub, .exec_fail h⟩
    · rcases ih () with ⟨r, hr⟩
      exact ⟨r, .exec_ok h hr⟩

/-- Key bridge lemma: if `e.StrictAll perm post` holds, then *every* `StepResult` produced by
    `BridgeEffects perm e` is `.next st' none` with `post st'` (never `.failed .ub` or
    `.failed .incomplete`). -/
theorem BridgeEffects.sound_of_strictAll {perm : PermPolicy} {e : Effects MachineState}
    {post : MachineState → Prop} {r : StepResult MachineState Unit}
    (hstrict : e.StrictAll perm post)
    (hbridge : BridgeEffects perm e r) :
    ∃ st', r = .next st' none ∧ post st' := by
  induction hbridge with
  | done st => exact ⟨st, rfl, hstrict⟩
  | undefined v _ ih =>
    dsimp [Effects.StrictAll] at hstrict
    exact ih (hstrict v)
  | unimplemented _ => exact False.elim hstrict
  | gp_unaligned _ => exact False.elim hstrict
  | nonmem_load _ _ => exact False.elim hstrict
  | nonmem_store _ _ => exact False.elim hstrict
  | read_ok _ _ ih => exact ih hstrict.2
  | read_fail hfalse =>
    rw [hstrict.1] at hfalse
    exact Bool.noConfusion hfalse
  | write_ok _ _ ih => exact ih hstrict.2
  | write_fail hfalse =>
    rw [hstrict.1] at hfalse
    exact Bool.noConfusion hfalse
  | exec_ok _ _ ih => exact ih hstrict.2
  | exec_fail hfalse =>
    rw [hstrict.1] at hfalse
    exact Bool.noConfusion hfalse

/-- Machine program packaging a Kraken `Executable Instr`, a designated halt PC `haltPc`,
    and the active `PermPolicy`. -/
structure HostedProgram where
  exe : Executable Instr
  haltPc : Nat
  perm : PermPolicy

def HostedProgram.stepEffect (hp : HostedProgram) (st : MachineState) :
    Option (Effects MachineState) :=
  if st.pc = hp.haltPc then
    none
  else
    match hp.exe.directivesAtAddress st.pc with
    | [] => some (.unimplemented "unmapped pc")
    | d :: rest =>
      let lastRange := ((d :: rest).getLast (List.cons_ne_nil d rest)).toAddressRange
      some (Directives.interp (d :: rest) st.data (fun s' => .done ⟨s', lastRange.upper⟩))

inductive KrakenMachineStep (hp : HostedProgram) (st : MachineState) :
    StepResult MachineState Unit → Prop where
  | at_halt :
    st.pc = hp.haltPc →
    KrakenMachineStep hp st .halted
  | step_eff {e : Effects MachineState} {r : StepResult MachineState Unit} :
    st.pc ≠ hp.haltPc →
    hp.stepEffect st = some e →
    BridgeEffects hp.perm e r →
    KrakenMachineStep hp st r

@[reducible] def KrakenMachine : SmallStepMachine where
  Prog := HostedProgram
  State := MachineState
  Obs := Unit
  step := KrakenMachineStep
  step_nonempty := fun hp st => by
    by_cases hpc : st.pc = hp.haltPc
    · exact ⟨.halted, .at_halt hpc⟩
    · cases hd : hp.exe.directivesAtAddress st.pc with
      | nil =>
        rcases BridgeEffects.nonempty hp.perm (.unimplemented "unmapped pc") with ⟨r, hr⟩
        refine ⟨r, .step_eff hpc ?_ hr⟩
        unfold HostedProgram.stepEffect
        simp [hpc, hd]
      | cons d rest =>
        let lastRange := ((d :: rest).getLast (List.cons_ne_nil d rest)).toAddressRange
        let eff := Directives.interp (d :: rest) st.data (fun s' => .done ⟨s', lastRange.upper⟩)
        rcases BridgeEffects.nonempty hp.perm eff with ⟨r, hr⟩
        refine ⟨r, .step_eff hpc ?_ hr⟩
        unfold HostedProgram.stepEffect
        simp [hpc, hd, eff, lastRange]

theorem KrakenMachineStep.sound_of_step1Strict {hp : HostedProgram} {st : MachineState}
    {post : MachineState → Prop} {r : StepResult MachineState Unit}
    (hne : st.pc ≠ hp.haltPc)
    (hstep1 : step1Strict hp.perm hp.exe st post)
    (hmstep : KrakenMachineStep hp st r) :
    ∃ st', r = .next st' none ∧ post st' := by
  cases hmstep with
  | at_halt hpc => exact False.elim (hne hpc)
  | step_eff _ heff hbridge =>
    unfold step1Strict at hstep1
    unfold HostedProgram.stepEffect at heff
    simp only [hne, ↓reduceIte] at heff
    split at hstep1
    · exact False.elim hstep1
    · rename_i d rest hds
      simp only [hds, Option.some.injEq] at heff
      rw [← heff] at hbridge
      exact BridgeEffects.sound_of_strictAll hstep1 hbridge

/-! ## Section 7: Concrete End-to-End Proofs (Positive Refinement & Negative Controls) -/

/-- Concrete hosted X64 program:
    index 0: `.label "entry"` (0 bytes at pc = 0)
    index 1: `.instr (.store64 0x1000 42)` (4 bytes at pc = 0..4)
    index 2: `.instr (.load64 0x1000)` (4 bytes at pc = 4..8) -/
def demoProg : Program Instr :=
  [.label "entry", .instr (.store64 0x1000 42), .instr (.load64 0x1000)]

@[reducible] def demoLayout : Layout Instr where
  size := fun _ => 4

instance demoHost : Host where
  prog := demoProg
  layout := demoLayout
  zero_inert := by
    intro i d _ hsz
    change 4 = 0 at hsz
    exact Nat.noConfusion hsz
  addr_determines_offset := by
    intro j k h
    exact h

def demoPerm : PermPolicy where
  canRead := fun addr bytes => decide (addr = 0x1000 ∧ bytes = 8)
  canWrite := fun addr bytes => decide (addr = 0x1000 ∧ bytes = 8)
  canExec := fun r => decide ((r.addr = 0 ∧ r.size = 4) ∨ (r.addr = 4 ∧ r.size = 4))

def demoInitData : MachineData where
  reg0 := 0
  mem0 := fun a => if a = 0x1000 then some 0 else none

/-- Verify that `directivesAtAddress 0` for `demoHost.exe` returns `[.label "entry", .instr (.store64 0x1000 42)]`,
    confirming `Host.directivesAtAddress_addrOf`: the 0-sized `.label "entry"` is grouped with the
    first positive-sized instruction at address 0! -/
theorem demo_directivesAtAddress_0 :
    Host.exe.directivesAtAddress 0 =
      [ ⟨⟨0, 0⟩, .label "entry"⟩,
        ⟨⟨0, 4⟩, .instr (.store64 0x1000 42)⟩ ] := by
  rfl

theorem demo_directivesAtAddress_4 :
    Host.exe.directivesAtAddress 4 =
      [ ⟨⟨4, 4⟩, .instr (.load64 0x1000)⟩ ] := by
  rfl

/-- Concrete `Program.wpStrict` proof for the full 3-directive `demoProg`. -/
theorem demoProg_wpStrict_at_0 :
    Eventually (step1Strict demoPerm Host.exe)
      (fun st => st.pc = 8 ∧ st.data.reg0 = 42)
      ⟨demoInitData, 0⟩ := by
  refine .step (Q := fun st => st.pc = 4 ∧ st.data.mem0 0x1000 = some 42) ?_ ?_
  · unfold step1Strict
    rw [demo_directivesAtAddress_0]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro st1 ⟨hpc1, hmem1⟩
    refine .step (Q := fun st => st.pc = 8 ∧ st.data.reg0 = 42) ?_ ?_
    · unfold step1Strict
      rw [hpc1, demo_directivesAtAddress_4]
      dsimp [Directives.interp, Directive.interp, Instr.interp, Effects.StrictAll,
        demoPerm, Width.bytes, AddressRange.upper]
      rw [hmem1]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · intro st2 hst2
      exact .now hst2

def demoHostedProg : HostedProgram where
  exe := Host.exe
  haltPc := 8
  perm := demoPerm

theorem ReachesPrefix.inv_succ {M : SmallStepMachine} {p : M.Prog}
    {n : Nat} {s : M.State} {tr : List M.Obs} {out : PrefixOutcome M.State}
    (h : ReachesPrefix M p (n + 1) s tr out) :
    (∃ s', M.step p s (.next s' none) ∧ ReachesPrefix M p n s' tr out) ∨
    (M.step p s .halted ∧ tr = [] ∧ out = .halted s) ∨
    (∃ k, M.step p s (.failed k) ∧ tr = [] ∧ out = .failed k) := by
  generalize hm : n + 1 = m at h
  cases h with
  | zero => exact False.elim (Nat.succ_ne_zero n hm)
  | step_next hs hrest =>
    injection hm with hnm
    subst hnm
    exact Or.inl ⟨_, hs, hrest⟩
  | step_halted hs =>
    exact Or.inr (Or.inl ⟨hs, rfl, rfl⟩)
  | step_failed hs =>
    exact Or.inr (Or.inr ⟨_, hs, rfl, rfl⟩)

theorem demoHostedProg_reach_3 {st0 : MachineState} {tr : List Unit}
    {out : PrefixOutcome MachineState}
    (hst0 : st0 = ⟨demoInitData, 0⟩)
    (hreach : ReachesPrefix KrakenMachine demoHostedProg 3 st0 tr out) :
    ∃ stFinal, out = .halted stFinal ∧ stFinal.pc = 8 ∧ stFinal.data.reg0 = 42 := by
  have hstep1 : step1Strict demoPerm Host.exe st0
      (fun st => st.pc = 4 ∧ st.data.mem0 0x1000 = some 42) := by
    rw [hst0]
    unfold step1Strict
    rw [demo_directivesAtAddress_0]
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hne1 : st0.pc ≠ demoHostedProg.haltPc := by rw [hst0]; decide
  rcases hreach.inv_succ with ⟨st1, hm1, hreach2⟩ | ⟨hm1, _, _⟩ | ⟨_, hm1, _, _⟩
  · rcases KrakenMachineStep.sound_of_step1Strict hne1 hstep1 hm1 with ⟨st1', hnext1, hpc1, hmem1⟩
    injection hnext1 with hst1
    subst hst1
    have hstep2 : step1Strict demoPerm Host.exe st1
        (fun st => st.pc = 8 ∧ st.data.reg0 = 42) := by
      unfold step1Strict
      rw [hpc1, demo_directivesAtAddress_4]
      dsimp [Directives.interp, Directive.interp, Instr.interp, Effects.StrictAll,
        demoPerm, Width.bytes, AddressRange.upper]
      rw [hmem1]
      exact ⟨rfl, rfl, rfl, rfl⟩
    have hne2 : st1.pc ≠ demoHostedProg.haltPc := by rw [hpc1]; decide
    rcases hreach2.inv_succ with ⟨st2, hm2, hreach3⟩ | ⟨hm2, _, _⟩ | ⟨_, hm2, _, _⟩
    · rcases KrakenMachineStep.sound_of_step1Strict hne2 hstep2 hm2 with ⟨st2', hnext2, hpc2, hreg2⟩
      injection hnext2 with hst2
      subst hst2
      rcases hreach3.inv_succ with ⟨_, hm3, _⟩ | ⟨hm3, _, hout⟩ | ⟨_, hm3, _, _⟩
      · cases hm3 with
        | step_eff hne3 _ _ => exact absurd hpc2 hne3
      · exact ⟨st2, hout, hpc2, hreg2⟩
      · cases hm3 with
        | step_eff hne3 _ _ => exact absurd hpc2 hne3
    · rcases KrakenMachineStep.sound_of_step1Strict hne2 hstep2 hm2 with ⟨_, hnext2, _⟩
      nomatch hnext2
    · rcases KrakenMachineStep.sound_of_step1Strict hne2 hstep2 hm2 with ⟨_, hnext2, _⟩
      nomatch hnext2
  · rcases KrakenMachineStep.sound_of_step1Strict hne1 hstep1 hm1 with ⟨_, hnext, _⟩
    nomatch hnext
  · rcases KrakenMachineStep.sound_of_step1Strict hne1 hstep1 hm1 with ⟨_, hnext, _⟩
    nomatch hnext

/-- Positive End-to-End Bridge Theorem:
    Running `demoHostedProg` for 3 steps (`step 1`: label+store64 at pc=0 -> pc=4;
    `step 2`: load64 at pc=4 -> pc=8; `step 3`: halts at `haltPc = 8`) in Anneal's
    `KrakenMachine` refines `(KrakenMachine.toLanguage).SpecOn` and `WellFormedOn`! -/
theorem demoHostedProg_refines_SpecOn :
    let L := KrakenMachine.toLanguage
    let pre : ExecQuery MachineState → Prop :=
      fun q => q.init = ⟨demoInitData, 0⟩ ∧ q.steps = 3
    let Post : ExecQuery MachineState → (List Unit × PrefixOutcome MachineState) → Prop :=
      fun _ pair => ∃ stFinal, pair.2 = .halted stFinal ∧ stFinal.pc = 8 ∧ stFinal.data.reg0 = 42
    BehaviorOf KrakenMachine demoHostedProg ≤ L.SpecOn pre Post ∧
    BehaviorOf KrakenMachine demoHostedProg ≤ L.WellFormedOn pre := by
  intro L pre Post
  have hmain : BehaviorOf KrakenMachine demoHostedProg ≤ L.SpecOn pre Post := by
    intro q ⟨hq_init, hq_steps⟩
    refine ⟨?_, ?_⟩
    · intro tr out hreach
      rw [hq_steps] at hreach
      rcases demoHostedProg_reach_3 hq_init hreach with ⟨stFinal, hout, _, _⟩
      rw [hout]
      trivial
    · intro pair hreach
      change ReachesPrefix KrakenMachine demoHostedProg q.steps q.init pair.1 pair.2 at hreach
      rw [hq_steps] at hreach
      exact demoHostedProg_reach_3 hq_init hreach
  refine ⟨hmain, Preorder.le_trans hmain ?_⟩
  intro q hpre
  exact ⟨hpre, fun _ _ => trivial⟩

/-- Negative Control 1:
    An unauthorized write `.instr (.store64 0x9999 77)` to an address mapped in `MachineData.mem0`
    but forbidden by `demoPerm.canWrite` STILL satisfies Kraken's default `Effects.All` (and hence
    `step1` / `Program.wp`), yet FAILS `Effects.StrictAll demoPerm` and transitions `KrakenMachine`
    to `.failed .ub`, making `(BehaviorOf KrakenMachine ...).defined` FALSE! -/
def unauthorizedWriteProg : Executable Instr :=
  demoLayout.apply [.instr (.store64 0x9999 77)]

def stateMappedAt0x9999 : MachineData where
  reg0 := 0
  mem0 := fun _ => some 0

theorem unauthorizedWrite_passes_default_step1_but_fails_Strict_and_Anneal :
    step1 unauthorizedWriteProg ⟨stateMappedAt0x9999, 0⟩ (fun st => st.pc = 4) ∧
    ¬ step1Strict demoPerm unauthorizedWriteProg ⟨stateMappedAt0x9999, 0⟩ (fun _ => True) ∧
    ¬ (BehaviorOf KrakenMachine
        { exe := unauthorizedWriteProg, haltPc := 4, perm := demoPerm }
        { init := ⟨stateMappedAt0x9999, 0⟩, steps := 1 }).defined := by
  refine ⟨rfl, ?_, ?_⟩
  · intro hstrict
    exact Bool.noConfusion hstrict.2.1
  · intro hdef
    have hmstep : KrakenMachineStep
        { exe := unauthorizedWriteProg, haltPc := 4, perm := demoPerm }
        ⟨stateMappedAt0x9999, 0⟩
        (.failed .ub) := by
      refine .step_eff (by decide) rfl ?_
      refine .exec_ok (by decide) ?_
      exact .write_fail rfl
    have hreach : ReachesPrefix KrakenMachine
        { exe := unauthorizedWriteProg, haltPc := 4, perm := demoPerm }
        1 ⟨stateMappedAt0x9999, 0⟩ [] (.failed .ub) :=
      .step_failed hmstep
    exact hdef [] (.failed .ub) hreach

/-- Negative Control 2:
    Executing `.byteArray [0x90]` emits `.unimplemented`, which fails both `step1` and `step1Strict`
    and transitions `KrakenMachine` to `.failed .incomplete`, refuting `(BehaviorOf ...).defined`. -/
def byteArrayExecProg : Executable Instr :=
  demoLayout.apply [.byteArray [0x90]]

theorem byteArrayExec_fails_step1_and_Anneal_defined :
    ¬ step1 byteArrayExecProg ⟨demoInitData, 0⟩ (fun _ => True) ∧
    ¬ (BehaviorOf KrakenMachine
        { exe := byteArrayExecProg, haltPc := 1, perm := demoPerm }
        { init := ⟨demoInitData, 0⟩, steps := 1 }).defined := by
  refine ⟨?_, ?_⟩
  · intro h
    exact h
  · intro hdef
    have hmstep : KrakenMachineStep
        { exe := byteArrayExecProg, haltPc := 1, perm := demoPerm }
        ⟨demoInitData, 0⟩
        (.failed .incomplete) := by
      refine .step_eff (by decide) rfl ?_
      exact .unimplemented "Unimplemented: execution reached data block"
    have hreach : ReachesPrefix KrakenMachine
        { exe := byteArrayExecProg, haltPc := 1, perm := demoPerm }
        1 ⟨demoInitData, 0⟩ [] (.failed .incomplete) :=
      .step_failed hmstep
    exact hdef [] (.failed .incomplete) hreach

/-! ## Section 8: Axiom Audit (`#guard_msgs` + `#print axioms`) -/

/-- info: 'KrakenWPAndBridgeProbe.Program.wp_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Program.wp_cons

/-- info: 'KrakenWPAndBridgeProbe.Host.eventually_of_interp_decomp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Host.eventually_of_interp_decomp

/-- info: 'KrakenWPAndBridgeProbe.Program.step1_of_wp_at' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Program.step1_of_wp_at

/-- info: 'KrakenWPAndBridgeProbe.nop0_not_strict_inert_when_unexec' does not depend on any axioms -/
#guard_msgs in
#print axioms nop0_not_strict_inert_when_unexec

/-- info: 'KrakenWPAndBridgeProbe.vmovupsLoad256_passes_buggy_W64_perm_check' does not depend on any axioms -/
#guard_msgs in
#print axioms vmovupsLoad256_passes_buggy_W64_perm_check

/-- info: 'KrakenWPAndBridgeProbe.demoProg_wpStrict_at_0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms demoProg_wpStrict_at_0

/-- info: 'KrakenWPAndBridgeProbe.demoHostedProg_refines_SpecOn' depends on axioms: [propext] -/
#guard_msgs in
#print axioms demoHostedProg_refines_SpecOn

/-- info: 'KrakenWPAndBridgeProbe.unauthorizedWrite_passes_default_step1_but_fails_Strict_and_Anneal' depends on axioms: [propext] -/
#guard_msgs in
#print axioms unauthorizedWrite_passes_default_step1_but_fails_Strict_and_Anneal

/-- info: 'KrakenWPAndBridgeProbe.byteArrayExec_fails_step1_and_Anneal_defined' depends on axioms: [propext] -/
#guard_msgs in
#print axioms byteArrayExec_fails_step1_and_Anneal_defined

end KrakenWPAndBridgeProbe
