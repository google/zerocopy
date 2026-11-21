/-!
# Indexed stores versus association-list stores

A store interface with get/put laws, the indexed store (a total function `Fin N → V`) and an
association-list store, representation independence of a certificate checker written against
the interface, and a toy cost model counting primitive store operations.
-/

namespace Toy.SlotCompact

/-- A store interface over keys `Fin N` and values `V`, with representation type `S`. -/
structure StoreOps (S : Type) (N : Nat) (V : Type) where
  get : S → Fin N → V
  put : S → Fin N → V → S

variable {S S₁ S₂ V : Type} {N : Nat}

/-- Reading a key just written returns the written value. -/
def GetPutSame (ops : StoreOps S N V) : Prop := ∀ s k v, ops.get (ops.put s k v) k = v

/-- Framing: writing one key does not change any other key. -/
def GetPutOther (ops : StoreOps S N V) : Prop :=
  ∀ s k k' v, k' ≠ k → ops.get (ops.put s k v) k' = ops.get s k'

/-- Writing back the current value leaves the representation unchanged (a representation-level
law, stronger than anything observable through `get`). -/
def PutGetId (ops : StoreOps S N V) : Prop := ∀ s k, ops.put s k (ops.get s k) = s

/-- A second write to the same key overrides the first (representation-level). -/
def PutPut (ops : StoreOps S N V) : Prop := ∀ s k v w, ops.put (ops.put s k v) k w = ops.put s k w

/-- The indexed store: a total function from slots to values. -/
def funOps (N : Nat) (V : Type) : StoreOps (Fin N → V) N V where
  get σ k := σ k
  put σ k v := fun j => if j = k then v else σ j

/-- Association-list lookup: the first entry with the key wins; a missing key reads as `d`. -/
def alistGet (d : V) : List (Fin N × V) → Fin N → V
  | [], _ => d
  | (k', v) :: l, k => if k' = k then v else alistGet d l k

/-- Association-list update: replace the first entry with the key, or append a new entry. -/
def alistPut : List (Fin N × V) → Fin N → V → List (Fin N × V)
  | [], k, v => [(k, v)]
  | (k', v') :: l, k, v => if k' = k then (k, v) :: l else (k', v') :: alistPut l k v

/-- The association-list store, with default value `d` for missing keys. -/
def alistOps (N : Nat) (d : V) : StoreOps (List (Fin N × V)) N V := ⟨alistGet d, alistPut⟩

/-- An association list is complete if every key has an entry. -/
def Complete (l : List (Fin N × V)) : Prop := ∀ k : Fin N, k ∈ l.map Prod.fst

theorem funOps_laws (N : Nat) (V : Type) :
    GetPutSame (funOps N V) ∧ GetPutOther (funOps N V) ∧ PutGetId (funOps N V) ∧
      PutPut (funOps N V) := by
  refine ⟨fun s k v => by simp [funOps], fun s k k' v h => by simp [funOps, h],
    fun s k => ?_, fun s k v w => ?_⟩
  · funext j; by_cases h : j = k <;> simp [funOps, h]
  · funext j; by_cases h : j = k <;> simp [funOps, h]

theorem alistGet_put_same (d : V) (l : List (Fin N × V)) (k : Fin N) (v : V) :
    alistGet d (alistPut l k v) k = v := by
  induction l with
  | nil => simp [alistGet, alistPut]
  | cons a l ih =>
    obtain ⟨k', v'⟩ := a
    by_cases h : k' = k <;> simp [alistPut, alistGet, h, ih]

theorem alistGet_put_other (d : V) (l : List (Fin N × V)) {k j : Fin N} (v : V) (hjk : j ≠ k) :
    alistGet d (alistPut l k v) j = alistGet d l j := by
  induction l with
  | nil => simp [alistGet, alistPut, Ne.symm hjk]
  | cons a l ih =>
    obtain ⟨k', v'⟩ := a
    by_cases h : k' = k
    · subst h; simp [alistPut, alistGet, Ne.symm hjk]
    · simp [alistPut, alistGet, h, ih]

theorem alistPut_put (l : List (Fin N × V)) (k : Fin N) (v w : V) :
    alistPut (alistPut l k v) k w = alistPut l k w := by
  induction l with
  | nil => simp [alistPut]
  | cons a l ih =>
    obtain ⟨k', v'⟩ := a
    by_cases h : k' = k <;> simp [alistPut, h, ih]

theorem alistPut_get_of_mem (d : V) (l : List (Fin N × V)) (k : Fin N)
    (hk : k ∈ l.map Prod.fst) : alistPut l k (alistGet d l k) = l := by
  induction l with
  | nil => simp at hk
  | cons a l ih =>
    obtain ⟨k', v'⟩ := a
    by_cases h : k' = k
    · subst h; simp [alistPut, alistGet]
    · have hk' : k ∈ l.map Prod.fst := by
        simp only [List.map_cons, List.mem_cons] at hk
        rcases hk with hk | hk
        · exact absurd hk.symm h
        · exact hk
      simp [alistPut, alistGet, h, ih hk']

/-- **Laws on the common domain.** The association-list store satisfies the observational laws
(`GetPutSame`, `GetPutOther`) and `PutPut` on all lists, and `PutGetId` on complete lists. -/
theorem alistOps_laws (N : Nat) (d : V) :
    GetPutSame (alistOps N d) ∧ GetPutOther (alistOps N d) ∧ PutPut (alistOps N d) ∧
      ∀ l : List (Fin N × V), Complete l → ∀ k, (alistOps N d).put l k ((alistOps N d).get l k) = l :=
  ⟨fun l k v => alistGet_put_same d l k v, fun l _ _ v h => alistGet_put_other d l v h,
    fun l k v w => alistPut_put l k v w, fun l hl k => alistPut_get_of_mem d l k (hl k)⟩

/-- With at least one slot, the empty association list is incomplete and violates `PutGetId`:
writing back the value read for slot `0` appends an entry. -/
theorem alistOps_empty_not_putGetId (N : Nat) (d : V) :
    ¬ Complete ([] : List (Fin (N + 1) × V)) ∧
      (alistOps (N + 1) d).put [] ⟨0, Nat.zero_lt_succ N⟩
        ((alistOps (N + 1) d).get [] ⟨0, Nat.zero_lt_succ N⟩) ≠ [] := by
  refine ⟨fun h => by simpa using h ⟨0, Nat.zero_lt_succ N⟩, ?_⟩
  simp [alistOps, alistPut]

/-- Consequently, with at least one slot the association-list store violates `PutGetId`. -/
theorem alistOps_not_putGetId (N : Nat) (d : V) : ¬ PutGetId (alistOps (N + 1) d) :=
  fun h => (alistOps_empty_not_putGetId N d).2 (h [] _)

/-- With zero slots every association list is complete, and `PutGetId` holds. -/
theorem alistOps_zero_putGetId (d : V) : PutGetId (alistOps 0 d) :=
  fun _ k => Fin.elim0 k

/-- A shadowing association list: `put` prepends an entry (lookup still takes the first match). -/
def consPutOps (N : Nat) : StoreOps (List (Fin N × Nat)) N Nat :=
  ⟨alistGet 0, fun l k v => (k, v) :: l⟩

theorem consPutOps_getPutSame (N : Nat) : GetPutSame (consPutOps N) :=
  fun l k v => by simp [consPutOps, alistGet]

theorem consPutOps_getPutOther (N : Nat) : GetPutOther (consPutOps N) := by
  intro l k k' v hne
  simp [consPutOps, alistGet, Ne.symm hne]

/-- The shadowing store satisfies both observational laws but not `PutPut` (with at least one
slot): representation-level laws distinguish implementations that `get` cannot. -/
theorem consPutOps_not_putPut (N : Nat) : ¬ PutPut (consPutOps (N + 1)) := by
  intro h
  have := h [] ⟨0, Nat.zero_lt_succ N⟩ 1 2
  simp [consPutOps] at this

/-- Reading through an association list is a homomorphism onto the indexed store: the view of a
put is the put of the view. -/
theorem alistGet_put_view (d : V) (l : List (Fin N × V)) (k : Fin N) (v : V) :
    alistGet d (alistPut l k v) = (funOps N V).put (alistGet d l) k v := by
  funext j
  by_cases h : j = k
  · subst h; simp [funOps, alistGet_put_same]
  · simp [funOps, h, alistGet_put_other d l v h]

/-! ## A certificate checker written against the interface -/

/-- Commands of a certificate replay: `incr d s c` stores `s + c` into `d`; `check k v` asserts
that slot `k` holds `v`. -/
inductive Cmd (N : Nat) where
  | incr (dst src : Fin N) (c : Nat)
  | check (k : Fin N) (v : Nat)
  deriving DecidableEq, Repr

/-- The checker: replays the commands through `ops` and accepts iff every check succeeds. It
uses the store only through `get` and `put`. -/
def runCheck (ops : StoreOps S N Nat) : S → List (Cmd N) → Bool
  | _, [] => true
  | s, .incr d src c :: rest => runCheck ops (ops.put s d (ops.get s src + c)) rest
  | s, .check k v :: rest => decide (ops.get s k = v) && runCheck ops s rest

/-- **Representation independence.** Two store implementations satisfying `GetPutSame` and
`GetPutOther`, started from stores with the same view, give the checker the same verdict on every
command list. -/
theorem runCheck_eq_of_getPut (ops₁ : StoreOps S₁ N Nat) (ops₂ : StoreOps S₂ N Nat)
    (h1s : GetPutSame ops₁) (h1o : GetPutOther ops₁) (h2s : GetPutSame ops₂)
    (h2o : GetPutOther ops₂) (c : List (Cmd N)) (s₁ : S₁) (s₂ : S₂)
    (hview : ∀ k, ops₁.get s₁ k = ops₂.get s₂ k) : runCheck ops₁ s₁ c = runCheck ops₂ s₂ c := by
  induction c generalizing s₁ s₂ with
  | nil => rfl
  | cons cmd rest ih =>
    cases cmd with
    | incr d src c =>
      apply ih
      intro k
      by_cases hk : k = d
      · subst hk; rw [h1s, h2s, hview]
      · rw [h1o _ _ _ _ hk, h2o _ _ _ _ hk, hview]
    | check k v =>
      simp only [runCheck, hview k, ih s₁ s₂ hview]

/-- The indexed store and the association-list store give the same verdict from stores with the
same view. -/
theorem runCheck_funOps_eq_alistOps (d : Nat) (σ : Fin N → Nat) (l : List (Fin N × Nat))
    (hview : alistGet d l = σ) (c : List (Cmd N)) :
    runCheck (funOps N Nat) σ c = runCheck (alistOps N d) l c := by
  have ⟨fs, fo, _, _⟩ := funOps_laws N Nat
  have ⟨as, ao, _, _⟩ := alistOps_laws N d
  exact runCheck_eq_of_getPut _ _ fs fo as ao c σ l (fun k => by simp [funOps, alistOps, ← hview])

/-! ## Toy cost model -/

/-- A cost model assigns a primitive-operation count to each get and put. -/
structure CostModel (S : Type) (N : Nat) where
  getCost : S → Fin N → Nat
  putCost : S → Fin N → Nat

/-- Cost of a checker run: the sum of the costs of all gets and puts that `runCheck` performs.
Like `runCheck`, it stops at the first failing `check` (whose get is still charged). -/
def runCost (ops : StoreOps S N Nat) (cm : CostModel S N) : S → List (Cmd N) → Nat
  | _, [] => 0
  | s, .incr d src c :: rest =>
    cm.getCost s src + cm.putCost s d + runCost ops cm (ops.put s d (ops.get s src + c)) rest
  | s, .check k v :: rest =>
    cm.getCost s k + (if ops.get s k = v then runCost ops cm s rest else 0)

/-- Unit cost: every get and put costs one primitive operation (the usual model of an array
indexed by slot number; it is an assumption of the cost model, not derived from `funOps`). -/
def unitCost (S : Type) (N : Nat) : CostModel S N := ⟨fun _ _ => 1, fun _ _ => 1⟩

/-- Cells inspected by a linear scan for key `k` (every cell when the key is absent). -/
def scanCost : List (Fin N) → Fin N → Nat
  | [], _ => 0
  | k' :: l, k => if k' = k then 1 else 1 + scanCost l k

/-- Association-list store: a get or put costs the number of cells its scan inspects (appending
a missing key is not charged separately). -/
def alistCost (N : Nat) (V : Type) : CostModel (List (Fin N × V)) N :=
  ⟨fun l k => scanCost (l.map Prod.fst) k, fun l k => scanCost (l.map Prod.fst) k⟩

theorem scanCost_le (ks : List (Fin N)) (k : Fin N) : scanCost ks k ≤ ks.length := by
  induction ks with
  | nil => simp [scanCost]
  | cons a ks ih => simp only [scanCost, List.length_cons]; split <;> omega

theorem scanCost_append_of_not_mem (xs : List (Fin N)) (k : Fin N) (h : k ∉ xs) :
    scanCost (xs ++ [k]) k = xs.length + 1 := by
  induction xs with
  | nil => simp [scanCost]
  | cons a xs ih =>
    have ha : a ≠ k := fun hak => h (by simp [hak])
    have hx : k ∉ xs := fun hk => h (by simp [hk])
    simp [scanCost, ha, ih hx]
    omega

theorem alistPut_keys (l : List (Fin N × V)) (k : Fin N) (v : V) (hk : k ∈ l.map Prod.fst) :
    (alistPut l k v).map Prod.fst = l.map Prod.fst := by
  induction l with
  | nil => simp at hk
  | cons a l ih =>
    obtain ⟨k', v'⟩ := a
    by_cases h : k' = k
    · subst h; simp [alistPut]
    · have hk' : k ∈ l.map Prod.fst := by
        simp only [List.map_cons, List.mem_cons] at hk
        rcases hk with hk | hk
        · exact absurd hk.symm h
        · exact hk
      simp [alistPut, h, ih hk']

/-- **Unit-cost model.** Under the unit cost model, a run of any store implementation (with
representation type `S`) over a command list `c` costs at most `2 * c.length` primitive
operations, independent of the number of slots. -/
theorem runCost_unitCost_le (ops : StoreOps S N Nat) (s : S) (c : List (Cmd N)) :
    runCost ops (unitCost S N) s c ≤ 2 * c.length := by
  induction c generalizing s with
  | nil => simp [runCost]
  | cons cmd rest ih =>
    cases cmd with
    | incr d src k =>
      have := ih (ops.put s d (ops.get s src + k))
      simp only [runCost, unitCost, List.length_cons] at this ⊢
      omega
    | check k v =>
      have := ih s
      simp only [runCost, unitCost, List.length_cons] at this ⊢
      split <;> omega

/-- **Association-list store, toy cost upper bound.** On a complete association list `l`, a run
over the command list `c` costs at most `2 · c.length · l.length` cells scanned. (`l.length` is at
least the number of slots and may exceed it when keys repeat.) -/
theorem runCost_alistOps_le (d : Nat) (l : List (Fin N × Nat)) (hl : Complete l)
    (c : List (Cmd N)) : runCost (alistOps N d) (alistCost N Nat) l c ≤ 2 * c.length * l.length := by
  induction c generalizing l with
  | nil => simp [runCost]
  | cons cmd rest ih =>
    cases cmd with
    | incr dst src k =>
      have hkeys := alistPut_keys l dst (alistGet d l src + k) (hl dst)
      have hl' : Complete (alistPut l dst (alistGet d l src + k)) := fun j => by
        rw [hkeys]; exact hl j
      have hlen : (alistPut l dst (alistGet d l src + k)).length = l.length := by
        rw [← List.length_map (f := Prod.fst), hkeys, List.length_map]
      have h1 := scanCost_le (l.map Prod.fst) src
      have h2 := scanCost_le (l.map Prod.fst) dst
      have h3 := ih _ hl'
      rw [hlen] at h3
      simp only [runCost, alistCost, alistOps, List.length_map, List.length_cons] at h1 h2 h3 ⊢
      rw [Nat.mul_add, Nat.add_mul]
      omega
    | check j v =>
      have h1 := scanCost_le (l.map Prod.fst) j
      have h3 := ih l hl
      simp only [runCost, alistCost, List.length_map, List.length_cons] at h1 h3 ⊢
      rw [Nat.mul_add, Nat.add_mul]
      split <;> omega

/-- The family of inputs for the lower bound: a complete association list over `L + 1` slots in
key order (length `L + 1`, no repeated keys), all values `0`. -/
def famAlist (L : Nat) : List (Fin (L + 1) × Nat) := (List.finRange (L + 1)).map fun k => (k, 0)

/-- The family of scripts: `S` increments of the last slot. -/
def famScript (S L : Nat) : List (Cmd (L + 1)) := List.replicate S (.incr (Fin.last L) (Fin.last L) 1)

theorem scanCost_finRange_last (L : Nat) : scanCost (List.finRange (L + 1)) (Fin.last L) = L + 1 := by
  rw [List.finRange_succ_last, scanCost_append_of_not_mem]
  · simp
  · intro h
    simp only [List.mem_map] at h
    obtain ⟨a, _, ha⟩ := h
    exact absurd ha (Fin.ne_of_lt (Fin.castSucc_lt_last a))

/-- **Association-list store, toy cost lower bound.** On the family `famAlist L` /
`famScript S L` (`S` commands over `L + 1` slots), the association-list checker performs exactly
`2 S (L + 1)` primitive operations. -/
theorem runCost_alistOps_family (S L : Nat) :
    runCost (alistOps (L + 1) 0) (alistCost (L + 1) Nat) (famAlist L) (famScript S L) =
      2 * S * (L + 1) := by
  suffices h : ∀ l : List (Fin (L + 1) × Nat), l.map Prod.fst = List.finRange (L + 1) →
      runCost (alistOps (L + 1) 0) (alistCost (L + 1) Nat) l (famScript S L) = 2 * S * (L + 1) by
    apply h
    simp [famAlist, List.map_map, Function.comp_def]
  induction S with
  | zero => intro l _; simp [famScript, runCost]
  | succ S ih =>
    intro l hl
    have hmem : Fin.last L ∈ l.map Prod.fst := by rw [hl]; exact List.mem_finRange _
    have hkeys := alistPut_keys l (Fin.last L) (alistGet 0 l (Fin.last L) + 1) hmem
    have := ih _ (hkeys.trans hl)
    simp only [famScript, List.replicate_succ, runCost, alistCost, alistOps] at this ⊢
    rw [hl, scanCost_finRange_last, this]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
    omega

/-- **Unit-cost model on the same family:** any store implementation performs exactly `2 S`
primitive operations. -/
theorem runCost_unitCost_family {St : Type} (S L : Nat) (ops : StoreOps St (L + 1) Nat) (s : St) :
    runCost ops (unitCost St (L + 1)) s (famScript S L) = 2 * S := by
  induction S generalizing s with
  | zero => simp [famScript, runCost]
  | succ S ih =>
    simp only [famScript, List.replicate_succ, runCost, unitCost] at ih ⊢
    rw [ih]
    omega

end Toy.SlotCompact
