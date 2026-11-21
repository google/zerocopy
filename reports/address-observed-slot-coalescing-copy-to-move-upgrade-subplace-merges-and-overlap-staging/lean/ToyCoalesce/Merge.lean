import ToyCoalesce.ObsAnalysis

/-!
# Coalescing locals into (sub)places of other locals

A *merge forest* is a list of edges `child ↦ (parent, off)`: local `child` is placed at offset
`off` inside local `parent` (a field window, possibly of a field). Following edges to the end
gives each local its *root* and its root-relative offset; merges compose by adding offsets. The
coalesced program rewrites every place through the forest, erases the storage statements of every
local in a nontrivial class (merged locals and roots), and allocates each root once at entry.
-/

namespace Toy.Coalesce

/-- A merge edge: `child` is placed at offset `off` inside `parent`. -/
structure Edge where
  child : Nat
  parent : Nat
  off : Nat
  deriving DecidableEq, Repr

/-- A merge forest. -/
abbrev Forest := List Edge

/-- The edge leaving `x`, if any. -/
def Forest.parentOf (μ : Forest) (x : Nat) : Option Edge := μ.find? (·.child == x)

/-- Follow at most `n` edges from `x`, accumulating offsets. -/
def Forest.resolveF (μ : Forest) : Nat → Nat → Nat × Nat
  | 0, x => (x, 0)
  | n + 1, x =>
    match μ.parentOf x with
    | some e => let r := μ.resolveF n e.parent; (r.1, r.2 + e.off)
    | none => (x, 0)

/-- Root and root-relative offset of `x`. -/
def Forest.resolve (μ : Forest) (x : Nat) : Nat × Nat := μ.resolveF μ.length x

def Forest.root (μ : Forest) (x : Nat) : Nat := (μ.resolve x).1

def Forest.offset (μ : Forest) (x : Nat) : Nat := (μ.resolve x).2

/-- `x` occurs in some edge (it is merged, or something is merged into it). -/
def Forest.inClass (μ : Forest) (x : Nat) : Bool := μ.any fun e => e.child == x || e.parent == x

/-- Remove duplicates, keeping first occurrences. -/
def nubNat : List Nat → List Nat
  | [] => []
  | x :: xs => x :: (nubNat xs).filter (· != x)

/-- The roots of the nontrivial classes. -/
def Forest.roots (μ : Forest) : List Nat := nubNat (μ.map fun e => μ.root e.child)

/-- Every top-level call of `P` names an existing callee (`fn < P.fns.length`). The semantics
runs an absent callee as `P.fn fn = ⟨0, []⟩`, whose parameter is local `0`; this predicate
excludes such calls. -/
def CallsInBounds (P : Prog) : Prop :=
  P.code.all (fun st => match st with | .call fn _ => decide (fn < P.fns.length) | _ => true) = true

instance (P : Prog) : Decidable (CallsInBounds P) := by unfold CallsInBounds; infer_instance

/-- Well-formed forests for `P`: each local has at most one parent; edges join distinct existing
locals and the child's window fits inside the parent; following edges from any local of `P`
reaches a local with no parent within `μ.length` steps (acyclicity); no callee parameter is in a
nontrivial class; and every top-level call names an existing callee (`CallsInBounds`). -/
def ForestWF (P : Prog) (μ : Forest) : Prop :=
  (μ.map Edge.child).Nodup ∧
  (∀ e ∈ μ, e.child < P.nloc ∧ e.parent < P.nloc ∧ e.child ≠ e.parent ∧
    e.off + P.size e.child ≤ P.size e.parent) ∧
  (∀ x, x < P.nloc → μ.parentOf (μ.root x) = none) ∧
  (∀ c ∈ P.fns, μ.inClass c.prm = false) ∧
  CallsInBounds P

set_option synthInstance.maxSize 1024 in
instance (P : Prog) (μ : Forest) : Decidable (ForestWF P μ) := by
  unfold ForestWF; infer_instance

/-- Rewrite every place of an operand. -/
def Operand.mapPlaces (f : Place → Place) : Operand → Operand
  | .copy q => .copy (f q)
  | .move q => .move (f q)
  | .lit n => .lit n
  | .addrOf q => .addrOf (f q)
  | .load p l => .load (f p) l

/-- Rewrite every place of a statement (storage statements name locals and are unchanged). -/
def Stmt.mapPlaces (f : Place → Place) : Stmt → Stmt
  | .storageLive x => .storageLive x
  | .storageDead x => .storageDead x
  | .assign lhs rhs => .assign (f lhs) (rhs.map (Operand.mapPlaces f))
  | .store p v => .store (f p) (v.mapPlaces f)
  | .ptrEq a b => .ptrEq (a.mapPlaces f) (b.mapPlaces f)
  | .ptrInRange a b n => .ptrInRange (a.mapPlaces f) (b.mapPlaces f) n
  | .out o => .out (o.mapPlaces f)
  | .call fn a => .call fn (a.mapPlaces f)
  | .nop => .nop

/-- A place rewritten through the forest: `x.path` becomes `root.(offset x + path)`. -/
def Forest.mapPlace (μ : Forest) (q : Place) : Place :=
  ⟨μ.root q.base, μ.offset q.base + q.off, q.len⟩

/-- Rewrite one statement: storage statements of class members become `nop`. -/
def Forest.coalesceStmt (μ : Forest) : Stmt → Stmt
  | .storageLive x => if μ.inClass x then .nop else .storageLive x
  | .storageDead x => if μ.inClass x then .nop else .storageDead x
  | st => st.mapPlaces μ.mapPlace

/-- The coalesced program: roots allocated at entry, every statement rewritten. -/
def coalesce (μ : Forest) (P : Prog) : Prog :=
  { P with
    body := μ.roots.map Stmt.storageLive ++ P.body.map μ.coalesceStmt
    dtors := P.dtors.map μ.coalesceStmt
    fns := P.fns.map fun c => { c with body := c.body.map μ.coalesceStmt } }

/-- The single merge `x ↦ y.f`. -/
def single (x y f : Nat) : Forest := [⟨x, y, f⟩]

/-! ## The value-level condition -/

/-- The cell of the coalesced program that holds source cell `(loc, off)`. -/
def Forest.tcell (μ : Forest) (loc off : Nat) : Nat × Nat := (μ.root loc, μ.offset loc + off)

/-- Scan a log, remembering for each coalesced cell the source cell of its last data write;
fail if a read of a source cell finds that the last data write to its coalesced cell was to a
different source cell. Allocation resets are ignored (class members' storage statements are erased
by coalescing). -/
def clobberFreeAux (μ : Forest) : List Access → (Nat × Nat → Option (Nat × Nat)) → Bool
  | [], _ => true
  | e :: es, lw =>
    match e.kind with
    | .read =>
      (match lw (μ.tcell e.loc e.off) with
       | some c => c == (e.loc, e.off)
       | none => true) && clobberFreeAux μ es lw
    | .write =>
      clobberFreeAux μ es fun t => if t = μ.tcell e.loc e.off then some (e.loc, e.off) else lw t
    | .reset => clobberFreeAux μ es lw

/-- *No value clobber* in a log: every read of a source cell is served, in the coalesced memory,
by the last data write to that same source cell (or by no data write at all). -/
def NoValueClobber (μ : Forest) (log : List Access) : Prop :=
  clobberFreeAux μ log (fun _ => none) = true

instance (μ : Forest) (log : List Access) : Decidable (NoValueClobber μ log) := by
  unfold NoValueClobber; infer_instance

/-- Statement-granular value-level condition: no value clobber in the log of the source run under
*atomic* assignments (a statement's reads precede its writes), on every layout whose source run
is neither excluded nor undefined. This is the dynamic counterpart of the address-free
no-clobber condition of the cited slot-compaction package. -/
def NoValueClobberStmt (ms : MoveSem) (μ : Forest) (P : Prog) : Prop :=
  ∀ A, outcome ⟨ms, .atomic⟩ P A ≠ .ub → outcome ⟨ms, .atomic⟩ P A ≠ .badLayout →
    NoValueClobber μ (run ⟨ms, .atomic⟩ P A).log

/-! ## Lifetime notions -/

/-- `u` is allocated before top-level statement `t` according to the storage statements of the
top-level sequence (lexical storage liveness; static, since there is no control flow). -/
def lexLiveBefore (P : Prog) (u t : Nat) : Bool :=
  (P.code.take t).foldl (fun b st =>
    match st with
    | .storageLive x => if x == u then true else b
    | .storageDead x => if x == u then false else b
    | _ => b) false

/-- `u` is lexically allocated during tick `t`: before it, or allocated by it. -/
def LexLiveAt (P : Prog) (u t : Nat) : Bool :=
  lexLiveBefore P u t || (P.code.getD t .nop == .storageLive u)

/-- Statement `st` reads local `u` by name (callee bodies included). -/
def Stmt.readsByName (P : Prog) (u : Nat) (st : Stmt) : Bool :=
  let loc1 := fun (s : Stmt) => s.operands.any (Operand.readsName u) ||
    (match s with | .store p _ => p.base == u | _ => false)
  loc1 st || (match st with | .call fn _ => (P.fn fn).body.any loc1 | _ => false)

/-- Statement `st` writes local `u` by name: an assignment to a place based at `u`, a callee body
assigning to `u` by name, or a call passing a place based at `u` by `move` (which an in-place
callee may write through its parameter). -/
def Stmt.writesByName (P : Prog) (u : Nat) (st : Stmt) : Bool :=
  let loc1 := fun (s : Stmt) => match s with | .assign lhs _ => lhs.base == u | _ => false
  loc1 st || (match st with
    | .call fn a => (P.fn fn).body.any loc1 || (match a with | .move q => q.base == u | _ => false)
    | _ => false)

/-- Statement `st` is a call whose callee body reads or writes local `u` by name (a by-name read
of an operand, the pointer cell of a `store`, or the left side of an assignment). -/
def Stmt.calleeTouchesByName (P : Prog) (u : Nat) : Stmt → Bool
  | .call fn _ => (P.fn fn).body.any fun s =>
      s.operands.any (Operand.readsName u) ||
      (match s with | .store p _ => p.base == u | .assign lhs _ => lhs.base == u | _ => false)
  | _ => false

/-- Half-statement access points of `u`: point `2t` if top-level statement `t` reads `u` by name,
point `2t+1` if it writes `u` by name, and both points if `t` is a call whose callee body reads or
writes `u` by name. A callee body is a sequence of statements, so its accesses are not ordered
with respect to the read half and the write half of the call; marking both halves makes every
local the callee touches overlap every other local accessed at that tick. -/
def AccessPt (P : Prog) (u p : Nat) : Bool :=
  (P.code.getD (p / 2) .nop).calleeTouchesByName P u ||
  (if p % 2 = 0 then (P.code.getD (p / 2) .nop).readsByName P u
   else (P.code.getD (p / 2) .nop).writesByName P u)

/-- Lifetime notions used by an interference check. -/
inductive Notion where
  | lexical
  | precise
  deriving DecidableEq, Repr

/-- Membership of half-statement point `p` in the interval of `u` under a notion: lexical
storage liveness during tick `p / 2`, or the hull of `u`'s by-name access points (precise
liveness, from first definition or use to last use or definition). -/
def InIv (nt : Notion) (P : Prog) (u p : Nat) : Bool :=
  match nt with
  | .lexical => LexLiveAt P u (p / 2)
  | .precise =>
    (List.range (p + 1)).any (AccessPt P u) &&
    ((List.range (2 * P.code.length + 2)).filter (p ≤ ·)).any (AccessPt P u)

/-- The intervals of `u` (under `nu`) and `v` (under `nv`) share a half-statement point. -/
def IvOverlap (nu nv : Notion) (P : Prog) (u v : Nat) : Prop :=
  ∃ p, p < 2 * P.code.length + 2 ∧ InIv nu P u p = true ∧ InIv nv P v p = true

instance (nu nv : Notion) (P : Prog) (u v : Nat) : Decidable (IvOverlap nu nv P u v) := by
  unfold IvOverlap; infer_instance

/-- Lexical overlap: `u` and `v` are allocated during a common tick. -/
def LexOverlap (P : Prog) (u v : Nat) : Prop := IvOverlap .lexical .lexical P u v

instance (P : Prog) (u v : Nat) : Decidable (LexOverlap P u v) := by
  unfold LexOverlap; infer_instance

/-! ## The address-level condition -/

/-- `u` and `v` are in the same nontrivial class. -/
def Forest.sameClass (μ : Forest) (u v : Nat) : Bool :=
  μ.inClass u && μ.inClass v && μ.root u == μ.root v

/-- The root-relative windows of `u` and `v` intersect. Edge case: a size-`0` local whose offset
lies strictly inside the window of `v` counts as intersecting it, although it has no cells; the
checks that use this predicate are then conservative. -/
def Forest.windowsOverlap (μ : Forest) (P : Prog) (u v : Nat) : Bool :=
  decide (μ.offset u < μ.offset v + P.size v ∧ μ.offset v < μ.offset u + P.size u)

/-- Root-level address check: any two distinct address-taken locals of the same class whose
root-relative windows intersect are never lexically allocated during a common tick. -/
def ClassAddrDisjoint (P : Prog) (μ : Forest) : Prop :=
  ∀ u, u < P.nloc → ∀ v, v < P.nloc → u ≠ v → μ.sameClass u v = true →
    μ.windowsOverlap P u v = true → AddrTaken P u → AddrTaken P v → ¬ LexOverlap P u v

set_option synthInstance.maxSize 1024 in
instance (P : Prog) (μ : Forest) : Decidable (ClassAddrDisjoint P μ) := by
  unfold ClassAddrDisjoint; infer_instance

/-- The window-insensitive variant: any two distinct address-taken locals of the same class
are never lexically allocated during a common tick. -/
def ClassAddrDisjointW (P : Prog) (μ : Forest) : Prop :=
  ∀ u, u < P.nloc → ∀ v, v < P.nloc → u ≠ v → μ.sameClass u v = true →
    AddrTaken P u → AddrTaken P v → ¬ LexOverlap P u v

set_option synthInstance.maxSize 1024 in
instance (P : Prog) (μ : Forest) : Decidable (ClassAddrDisjointW P μ) := by
  unfold ClassAddrDisjointW; infer_instance

/-- The per-edge check (each merge checked against its immediate parent and no other local). -/
def EdgeAddrCheck (P : Prog) (μ : Forest) : Prop :=
  ∀ e ∈ μ, AddrTaken P e.child → AddrTaken P e.parent → ¬ LexOverlap P e.child e.parent

instance (P : Prog) (μ : Forest) : Decidable (EdgeAddrCheck P μ) := by
  unfold EdgeAddrCheck; infer_instance

/-- The member-versus-root check (each merged local checked against its root local and no other local). -/
def RootAddrCheck (P : Prog) (μ : Forest) : Prop :=
  ∀ u, u < P.nloc → μ.inClass u = true → u ≠ μ.root u → AddrTaken P u →
    AddrTaken P (μ.root u) → ¬ LexOverlap P u (μ.root u)

set_option synthInstance.maxSize 1024 in
instance (P : Prog) (μ : Forest) : Decidable (RootAddrCheck P μ) := by
  unfold RootAddrCheck; infer_instance

/-! ## Union–find with interval union -/

/-- A disjoint-set block: its members and the ticks at which some address-taken member is
lexically allocated (the union of their lexical intervals). -/
structure UFBlock where
  members : List Nat
  ticks : List Nat
  deriving DecidableEq, Repr

/-- Ticks at which `u` is lexically allocated, if `u` is address-taken (else none). -/
def aoTicks (P : Prog) (u : Nat) : List Nat :=
  if AddrTaken P u then (List.range (P.code.length + 1)).filter (LexLiveAt P u) else []

/-- Initial singleton blocks. -/
def ufInit (P : Prog) : List UFBlock := (List.range P.nloc).map fun u => ⟨[u], aoTicks P u⟩

/-- Process one edge: find both blocks, reject a cycle or intersecting tick unions, otherwise
replace the two blocks by their union. -/
def ufStep (bs : List UFBlock) (e : Edge) : Option (List UFBlock) :=
  match bs.find? (·.members.contains e.child), bs.find? (·.members.contains e.parent) with
  | some b1, some b2 =>
    if b1 = b2 then none
    else if b1.ticks.any (b2.ticks.contains ·) then none
    else some (⟨b1.members ++ b2.members, b1.ticks ++ b2.ticks⟩ ::
      bs.filter fun b => b != b1 && b != b2)
  | _, _ => none

/-- The union–find check: process every edge; accept iff no step rejects. -/
def ufCheck (P : Prog) (μ : Forest) : Bool := (μ.foldlM ufStep (ufInit P)).isSome

/-! ## Main statements -/

/-- For the single merge `x ↦ y.f`, the two-sided lexical condition on `x` and `y` implies the
root-level address check. -/
theorem classAddrDisjoint_single_of_lexDisjoint (P : Prog) (x y f : Nat)
    (hii : AddrTaken P x → AddrTaken P y → ¬ LexOverlap P x y) :
    ClassAddrDisjoint P (single x y f) := by
  intro u _ v _ hne hsc _ hau hav
  simp only [Forest.sameClass, Forest.inClass, single, List.any_cons, List.any_nil,
    Bool.or_false, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hsc
  rcases hsc with ⟨⟨hu' | hu', hv' | hv'⟩, _⟩
  · subst hu'; subst hv'; exact absurd rfl hne
  · subst hu'; subst hv'; exact hii hau hav
  · subst hu'; subst hv'
    intro ⟨p, hp, h1, h2⟩
    exact hii hav hau ⟨p, hp, h2, h1⟩
  · subst hu'; subst hv'; exact absurd rfl hne

/-- The window-insensitive check implies the window-sensitive one. -/
theorem classAddrDisjoint_of_classAddrDisjointW (P : Prog) (μ : Forest)
    (h : ClassAddrDisjointW P μ) : ClassAddrDisjoint P μ :=
  fun u hu v hv hne hc _ ha hb => h u hu v hv hne hc ha hb

/-- A coalescer interference policy: the lifetime notion used for address-taken locals
(`pol true`) and for the others (`pol false`). -/
abbrev Policy := Bool → Notion

/-- The policy check: distinct class members with intersecting root-relative windows have
non-overlapping intervals, each interval computed with the notion the policy assigns to that
local. -/
def PolicyCheck (pol : Policy) (P : Prog) (μ : Forest) : Prop :=
  ∀ u, u < P.nloc → ∀ v, v < P.nloc → u ≠ v → μ.sameClass u v = true →
    μ.windowsOverlap P u v = true →
    ¬ IvOverlap (pol (decide (AddrTaken P u))) (pol (decide (AddrTaken P v))) P u v

instance (pol : Policy) (P : Prog) (μ : Forest) : Decidable (PolicyCheck pol P μ) := by
  unfold PolicyCheck; infer_instance

/-- A policy is sound when every well-formed forest that passes its check yields a refinement,
under atomic assignments and every `move` semantics. -/
def PolicySound (pol : Policy) : Prop :=
  ∀ (ms : MoveSem) (P : Prog) (μ : Forest), ForestWF P μ → PolicyCheck pol P μ →
    Refines ⟨ms, .atomic⟩ (coalesce μ P) ⟨ms, .atomic⟩ P

end Toy.Coalesce
