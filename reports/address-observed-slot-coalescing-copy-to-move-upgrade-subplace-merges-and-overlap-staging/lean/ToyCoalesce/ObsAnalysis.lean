import ToyCoalesce.Upgrade

/-!
# A backward "may be read later" analysis licensing copy-to-move upgrades

A static, whole-local, backward analysis over the top-level statement sequence (body, then the
destructor block). Gen: by-name reads of a local, any `load` when the local is address-taken,
and the same reads inside a called callee (the callee summary). Kill: storage statements of the
local and assignments to the whole local. The analysis result is a mask that is *claimed* and
*checked* as a certificate, not trusted.
-/

namespace Toy.Coalesce

/-- Operand `o` reads a cell of local `u` by name: `copy`/`move` of a place based at `u`, or the
pointer cell of a `load` from a place based at `u`. -/
def Operand.readsName (u : Nat) : Operand → Bool
  | .copy q => q.base == u
  | .move q => q.base == u
  | .load p _ => p.base == u
  | _ => false

/-- Operand `o` is a load through a pointer. -/
def Operand.isLoad : Operand → Bool
  | .load _ _ => true
  | _ => false

/-- The operands evaluated by a statement. -/
def Stmt.operands : Stmt → List Operand
  | .assign _ rhs => rhs
  | .store _ v => [v]
  | .ptrEq a b => [a, b]
  | .ptrInRange a b _ => [a, b]
  | .out o => [o]
  | .call _ a => [a]
  | _ => []

/-- Statement `st` (ignoring callee bodies) may read a cell of local `u`: a by-name read
(including the pointer cell of a `store`), or a `load` when `u` is address-taken in `P`. -/
def Stmt.mayReadNoCall (P : Prog) (u : Nat) (st : Stmt) : Bool :=
  st.operands.any (Operand.readsName u) ||
  (match st with | .store p _ => p.base == u | _ => false) ||
  (decide (AddrTaken P u) && st.operands.any Operand.isLoad)

/-- Statement `st` may read a cell of local `u`, including reads inside the callee it calls (the
callee summary). -/
def Stmt.mayRead (P : Prog) (u : Nat) (st : Stmt) : Bool :=
  st.mayReadNoCall P u ||
  (match st with | .call fn _ => (P.fn fn).body.any (Stmt.mayReadNoCall P u) | _ => false)

/-- Statement `st` re-initializes every cell of local `u`: a storage statement of `u`, or an
assignment to the whole of `u`. -/
def Stmt.kills (P : Prog) (u : Nat) : Stmt → Bool
  | .storageLive x => x == u
  | .storageDead x => x == u
  | .assign lhs _ => lhs.base == u && lhs.off == 0 && lhs.len == P.size u
  | _ => false

/-- A claimed "may be read at or after this tick" mask: `O t u`. -/
abbrev ObsMask := Nat → Nat → Bool

/-- The certificate conditions over the whole top-level sequence (body and destructors): at every
tick `t` and for every local `u`, a possible read of `u` at `t` is in `O t u` (gen), and
`O (t+1) u` propagates to `O t u` unless the statement at `t` re-initializes `u` (transfer). -/
def ObsCert (P : Prog) (O : ObsMask) : Prop :=
  ∀ t, t < P.code.length → ∀ u, u < P.nloc →
    ((P.code.getD t .nop).mayRead P u = true → O t u = true) ∧
    (O (t + 1) u = true → (P.code.getD t .nop).kills P u = false → O t u = true)

/-- The same conditions checked over the body and not over the destructor block: a destructor-blind
analysis. -/
def ObsCertBodyOnly (P : Prog) (O : ObsMask) : Prop :=
  ∀ t, t < P.body.length → ∀ u, u < P.nloc →
    ((P.code.getD t .nop).mayRead P u = true → O t u = true) ∧
    (O (t + 1) u = true → (P.code.getD t .nop).kills P u = false → O t u = true)

/-- Boolean certificate checker. -/
def checkObs (P : Prog) (O : ObsMask) : Bool :=
  (List.range P.code.length).all fun t => (List.range P.nloc).all fun u =>
    (!(P.code.getD t .nop).mayRead P u || O t u) &&
    (!(O (t + 1) u && !(P.code.getD t .nop).kills P u) || O t u)

/-- The analysis computed by a backward scan: `u` may be read at or after the head of `sts`
before being re-initialized. -/
def obsFrom (P : Prog) (u : Nat) : List Stmt → Bool
  | [] => false
  | st :: sts => st.mayRead P u || (!st.kills P u && obsFrom P u sts)

/-- The computed mask. -/
def obsAnalysis (P : Prog) : ObsMask := fun t u => obsFrom P u (P.code.drop t)

/-- An upgrade at body index `k` of place `q` is *licensed* by the mask `O` under a `move`
semantics:
* `asCopy`: always;
* `deinit`: `q.base` is not in `O (k+1)`, and, for a call site, the callee summary does not read
  `q.base`;
* `inPlaceCall`: for a call site, `q.base` is not in `O (k+1)`, the callee does not read or assign
  a place based at `q.base` by name and does not store through a pointer held in such a place, it
  does no `load` and no `store` at all if `q.base` is address-taken, and the callee's parameter
  local is not address-taken anywhere in `P`; non-call sites are always licensed. -/
def Licensed (ms : MoveSem) (P : Prog) (O : ObsMask) (k : Nat) (q : Place) : Prop :=
  match ms with
  | .asCopy => True
  | .deinit =>
    O (k + 1) q.base = false ∧
    ∀ fn, P.body[k]? = some (.call fn (.copy q)) →
      (P.fn fn).body.any (Stmt.mayReadNoCall P q.base) = false
  | .inPlaceCall =>
    ∀ fn, P.body[k]? = some (.call fn (.copy q)) →
      O (k + 1) q.base = false ∧
      (P.fn fn).body.any (fun st => st.operands.any (Operand.readsName q.base) ||
        (match st with
         | .store p _ => p.base == q.base
         | .assign lhs _ => lhs.base == q.base
         | _ => false)) = false ∧
      (decide (AddrTaken P q.base) && (P.fn fn).body.any (fun st =>
        st.operands.any Operand.isLoad || (match st with | .store _ _ => true | _ => false)))
        = false ∧
      ¬ AddrTaken P (P.fn fn).prm

/-! ## Main statements -/

/-- The Boolean checker accepts exactly the masks satisfying the certificate conditions. -/
theorem checkObs_eq_true_iff (P : Prog) (O : ObsMask) : checkObs P O = true ↔ ObsCert P O := by
  simp only [checkObs, ObsCert, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro h t ht u hu
    have ⟨h1, h2⟩ := h t ht u hu
    constructor
    · intro hr
      rcases h1 with h1 | h1
      · rw [hr] at h1; cases h1
      · exact h1
    · intro hO hk
      rcases h2 with h2 | h2
      · rw [hO, hk] at h2; cases h2
      · exact h2
  · intro h t ht u hu
    have ⟨h1, h2⟩ := h t ht u hu
    constructor
    · cases hr : (P.code.getD t .nop).mayRead P u
      · exact Or.inl rfl
      · exact Or.inr (h1 hr)
    · cases hO : O (t + 1) u <;> cases hk : (P.code.getD t .nop).kills P u
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (h2 hO hk)
      · exact Or.inl rfl

/-- The computed mask is a certificate, and it is below every certificate (at every tick of the
top-level sequence, for every local of the program). -/
theorem obsAnalysis_least_cert (P : Prog) :
    ObsCert P (obsAnalysis P) ∧
    ∀ O, ObsCert P O → ∀ t, t ≤ P.code.length → ∀ u, u < P.nloc →
      obsAnalysis P t u = true → O t u = true := by
  have hdrop : ∀ t, (ht : t < P.code.length) →
      P.code.drop t = P.code[t] :: P.code.drop (t + 1) := fun t ht => List.drop_eq_getElem_cons ht
  have hget : ∀ t, (ht : t < P.code.length) → P.code.getD t .nop = P.code[t] := by
    intro t ht; simp [List.getD_eq_getElem?_getD, ht]
  refine ⟨?_, ?_⟩
  · intro t ht u _
    simp only [obsAnalysis, hdrop t ht, obsFrom, hget t ht]
    exact ⟨fun h => by simp [h], fun h hk => by simp [h, hk]⟩
  · intro O hO t ht u hu
    obtain ⟨n, hn⟩ : ∃ n, P.code.length = t + n := ⟨P.code.length - t, by omega⟩
    induction n generalizing t with
    | zero =>
      intro h
      have hd : P.code.drop t = [] := List.drop_eq_nil_of_le (by omega)
      simp [obsAnalysis, hd, obsFrom] at h
    | succ n ih =>
      intro h
      have ht' : t < P.code.length := by omega
      simp only [obsAnalysis, hdrop t ht', obsFrom, Bool.or_eq_true, Bool.and_eq_true,
        Bool.not_eq_true'] at h
      have hc := hO t ht' u hu
      rw [hget t ht'] at hc
      rcases h with h | ⟨hk, h⟩
      · exact hc.1 h
      · exact hc.2 (ih (t + 1) (by omega) (by omega) h) hk

end Toy.Coalesce
