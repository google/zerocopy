/-
# A total language of finite lookup tables (no fixpoint principle)

Codes are finite lookup tables; behaviours are total functions `ℕ → ℕ`. Admissible code
transformers are exactly those expressible in a small total transformer language `TProg`:
constant tables, the identity, two table edits (`setAt k n` prepends the entry `(k, n)`;
`incrAt k` prepends `(k, eval x k + 1)`), composition, and a conditional `branch p q r` on any
test `p` of a small test language `TTest`. Tests compare the value of the table at a fixed
input with a constant, or check that every entry of the table passes an entry test (comparing the
entry's listed output, or the table's value at the entry's key, with a constant), closed under
negation and conjunction. Every `TProg` program denotes a total function; `TProg` is not
Turing-complete, and the admissible class is a proper one: `List.tail` is not admissible.

The checker `zeroCheck` for "the table computes the zero function" is *programmed* as a test
(`allEntries (evalAtKeyEq 0)`), as are the syntactic checker `allOutputsZero`, the pointwise
check "the value at `0` is `0`", and "the table is empty". All of them are decided inside the
system. The fixpoint principle fails (`incrAt 0` changes every behaviour).

What this models: a deliberately weak total formalism (finite lookup tables) whose behaviours
have finite support, so that universally quantified behavioural properties reduce to finitely
many checks. It is not a model of primitive-recursive or other expressive total languages, in
which such properties can remain undecidable.
-/
import ToyRice.Basic

namespace Toy.Rice.Tables

/-- A finite lookup table: a list of `(input, output)` entries. Earlier entries shadow later
entries with the same input; inputs with no entry map to `0`. Different tables can have the
same behaviour (reordering, shadowed entries, explicit zero entries). -/
abbrev Table := List (Nat × Nat)

/-- Behaviour of a table: look up the first entry for the input, defaulting to `0`. -/
def eval : Table → Nat → Nat
  | [], _ => 0
  | (k, v) :: t, n => if n = k then v else eval t n

/-- "The table computes the zero function." Extensional. -/
def IsZeroFn (t : Table) : Prop := ∀ n, eval t n = 0

/-- Checker for `IsZeroFn`: evaluate the table at each of its own keys. -/
def zeroCheck (t : Table) : Bool := t.all (fun p => eval t p.1 == 0)

/-- A purely syntactic checker: every listed output is `0`. Sound but incomplete for
`IsZeroFn` (it rejects `[(0, 0), (0, 5)]`, whose second entry is shadowed). -/
def allOutputsZero (t : Table) : Bool := t.all (fun p => p.2 == 0)

/-- Tests on one entry `(k, v)` of a table `t`. -/
inductive EntryTest where
  /-- The listed output equals `n`: `v = n`. -/
  | valEq (n : Nat)
  /-- The table's value at the entry's key equals `n`: `eval t k = n`. -/
  | evalAtKeyEq (n : Nat)
  /-- Negation. -/
  | not (e : EntryTest)
  /-- Conjunction. -/
  | and (e f : EntryTest)

/-- Interpreter for entry tests. -/
def EntryTest.run (t : Table) (e : Nat × Nat) : EntryTest → Bool
  | .valEq n => e.2 == n
  | .evalAtKeyEq n => eval t e.1 == n
  | .not p => !(p.run t e)
  | .and p q => p.run t e && q.run t e

/-- Tests on a table. -/
inductive TTest where
  /-- The table's value at input `k` equals `n`. -/
  | evalAtEq (k n : Nat)
  /-- Every entry of the table passes the entry test. -/
  | allEntries (e : EntryTest)
  /-- Negation. -/
  | not (p : TTest)
  /-- Conjunction. -/
  | and (p q : TTest)

/-- Interpreter for table tests. -/
def TTest.run (t : Table) : TTest → Bool
  | .evalAtEq k n => eval t k == n
  | .allEntries e => t.all (fun p => e.run t p)
  | .not p => !(p.run t)
  | .and p q => p.run t && q.run t

/-- A small total language of table transformers. -/
inductive TProg where
  /-- The constant transformer with output `t`. -/
  | const (t : Table)
  /-- The identity. -/
  | ident
  /-- Set the value at input `k` to `n` (prepend the entry `(k, n)`). -/
  | setAt (k n : Nat)
  /-- Increment the value at input `k` (prepend the entry `(k, eval x k + 1)`). -/
  | incrAt (k : Nat)
  /-- `branch p q r` runs `q` on inputs passing the test `p` and `r` on the others. -/
  | branch (p : TTest) (q r : TProg)
  /-- `comp p q` runs `q`, then `p`. -/
  | comp (p q : TProg)

/-- Interpreter for `TProg`. Every program denotes a total function. -/
def TProg.run : TProg → Table → Table
  | .const t, _ => t
  | .ident, x => x
  | .setAt k n, x => (k, n) :: x
  | .incrAt k, x => (k, eval x k + 1) :: x
  | .branch p q r, x => cond (p.run x) (q.run x) (r.run x)
  | .comp p q, x => p.run (q.run x)

/-- A transformer is admissible when some `TProg` program computes it. -/
def Admissible (f : Table → Table) : Prop := ∃ p : TProg, ∀ x, p.run x = f x

/-- The lookup-table system. -/
def sys : System := ⟨Table, Nat → Nat, eval, Admissible⟩

/-- Every switch on a test-definable checker is admissible. -/
theorem switchAdmissible_of_test (p : TTest) : SwitchAdmissible sys (fun t => p.run t) :=
  fun a b => ⟨.branch p (.const a) (.const b), fun _ => rfl⟩

/-- `zeroCheck` is programmed as a test. -/
theorem zeroCheck_eq_test (t : Table) : zeroCheck t = TTest.run t (.allEntries (.evalAtKeyEq 0)) :=
  rfl

/-- `allOutputsZero` is programmed as a test. -/
theorem allOutputsZero_eq_test (t : Table) :
    allOutputsZero t = TTest.run t (.allEntries (.valEq 0)) := rfl

-- Small cases, checked by evaluation.
example : eval [(0, 0), (0, 5)] 0 = 0 := by decide
example : eval [(0, 0), (0, 5)] 1 = 0 := by decide
example : eval [(3, 7)] 3 = 7 := by decide
example : zeroCheck [] = true := by decide
example : zeroCheck [(0, 0), (0, 5)] = true := by decide
example : zeroCheck [(1, 0), (0, 5)] = false := by decide
example : allOutputsZero [(0, 0), (0, 5)] = false := by decide

theorem eval_ne_zero_exists_key (t : Table) (n : Nat) (h : eval t n ≠ 0) :
    ∃ p ∈ t, p.1 = n := by
  induction t with
  | nil => exact absurd rfl h
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    by_cases hnk : n = k
    · exact ⟨(k, v), List.mem_cons_self, hnk.symm⟩
    · have : eval t n ≠ 0 := by simpa [eval, hnk] using h
      obtain ⟨q, hq, hq1⟩ := ih this
      exact ⟨q, List.mem_cons_of_mem _ hq, hq1⟩

/-- `zeroCheck` decides `IsZeroFn`. -/
theorem zeroCheck_decides : Decides zeroCheck IsZeroFn := by
  intro t
  constructor
  · intro h n
    apply Classical.byContradiction
    intro hn
    obtain ⟨p, hp, hp1⟩ := eval_ne_zero_exists_key t n hn
    have := (List.all_eq_true.1 h) p hp
    simp only [beq_iff_eq] at this
    rw [hp1] at this
    exact hn this
  · intro h
    apply List.all_eq_true.2
    intro p _
    simp [h p.1]

theorem isZeroFn_extensional : Extensional sys IsZeroFn := by
  intro c d h
  show (∀ n, eval c n = 0) ↔ (∀ n, eval d n = 0)
  have h' : eval c = eval d := h
  rw [h']

theorem isZeroFn_nontrivial : NontrivialPred IsZeroFn :=
  ⟨⟨[], fun _ => rfl⟩, ⟨[(0, 1)], fun h => by have := h 0; simp [eval] at this⟩⟩

/-- Constants are admissible. -/
theorem constClosed : ConstClosed sys := fun k => ⟨.const k, fun _ => rfl⟩

/-- Admissible transformers are closed under composition. -/
theorem compClosed : CompClosed sys := by
  rintro f g ⟨p, hp⟩ ⟨q, hq⟩
  exact ⟨.comp p q, fun x => (hp (q.run x)).trans (congrArg f (hq x))⟩

/-- Every switch on `zeroCheck` is admissible (`zeroCheck` is a test). -/
theorem zeroCheck_switchAdmissible : SwitchAdmissible sys zeroCheck :=
  switchAdmissible_of_test (.allEntries (.evalAtKeyEq 0))

/-- Every switch on the syntactic checker `allOutputsZero` is admissible. -/
theorem allOutputsZero_switchAdmissible : SwitchAdmissible sys allOutputsZero :=
  switchAdmissible_of_test (.allEntries (.valEq 0))

/-- The pointwise extensional property "the value at `0` is `0`" is decided inside the system. -/
theorem evalAtZero_decidedInside : DecidedInside sys (fun t => eval t 0 = 0) :=
  ⟨fun t => TTest.run t (.evalAtEq 0 0), fun t => by simp [TTest.run],
    switchAdmissible_of_test _⟩

/-- The syntactic property "the table is empty" is decided inside the system. -/
theorem isNil_decidedInside : DecidedInside sys (fun t => t = []) := by
  refine ⟨fun t => TTest.run t (.allEntries (.and (.valEq 0) (.not (.valEq 0)))), fun t => ?_,
    switchAdmissible_of_test _⟩
  cases t with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons p t => simp [TTest.run, EntryTest.run]

/-- In the lookup-table system, `IsZeroFn` is decided inside the system. -/
theorem isZeroFn_decidedInside : DecidedInside sys IsZeroFn :=
  ⟨zeroCheck, zeroCheck_decides, zeroCheck_switchAdmissible⟩

/-- The transformer that increments the value at input `0` (the program `incrAt 0`). -/
def bump (t : Table) : Table := (0, eval t 0 + 1) :: t

theorem bump_admissible : sys.Adm bump := ⟨.incrAt 0, fun _ => rfl⟩

/-- The lookup-table system has no fixpoint principle: `bump` changes every behaviour. -/
theorem not_fixpointPrinciple : ¬ FixpointPrinciple sys := by
  intro hfix
  obtain ⟨c, hc⟩ := hfix bump bump_admissible
  have h0 := congrFun hc 0
  change eval ((0, eval c 0 + 1) :: c) 0 = eval c 0 at h0
  simp [eval] at h0

/-! ## The admissible class is a proper class -/

/-- Every admissible transformer either has output in a fixed finite set or does not shorten
its input. -/
theorem run_finite_or_length_le (p : TProg) :
    ∃ L : List Table, ∀ x, p.run x ∈ L ∨ x.length ≤ (p.run x).length := by
  induction p with
  | const t => exact ⟨[t], fun _ => Or.inl (List.mem_singleton.2 rfl)⟩
  | ident => exact ⟨[], fun _ => Or.inr (Nat.le_refl _)⟩
  | setAt k n => exact ⟨[], fun x => Or.inr (by simp [TProg.run])⟩
  | incrAt k => exact ⟨[], fun x => Or.inr (by simp [TProg.run])⟩
  | branch c p q ihp ihq =>
    obtain ⟨Lp, hp⟩ := ihp
    obtain ⟨Lq, hq⟩ := ihq
    refine ⟨Lp ++ Lq, fun x => ?_⟩
    cases hz : c.run x with
    | true =>
      simp only [TProg.run, hz, Bool.cond_true]
      rcases hp x with h | h
      · exact Or.inl (List.mem_append_left _ h)
      · exact Or.inr h
    | false =>
      simp only [TProg.run, hz, Bool.cond_false]
      rcases hq x with h | h
      · exact Or.inl (List.mem_append_right _ h)
      · exact Or.inr h
  | comp p q ihp ihq =>
    obtain ⟨Lp, hp⟩ := ihp
    obtain ⟨Lq, hq⟩ := ihq
    refine ⟨Lq.map p.run ++ Lp, fun x => ?_⟩
    simp only [TProg.run]
    rcases hq x with h | h
    · exact Or.inl (List.mem_append_left _ (List.mem_map_of_mem h))
    · rcases hp (q.run x) with h' | h'
      · exact Or.inl (List.mem_append_right _ h')
      · exact Or.inr (Nat.le_trans h h')

theorem exists_long (L : List Table) : ∃ N, ∀ t ∈ L, t.length < N := by
  induction L with
  | nil => exact ⟨0, fun _ h => absurd h List.not_mem_nil⟩
  | cons s L ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨max (s.length + 1) N, fun t ht => ?_⟩
    rcases List.mem_cons.1 ht with h | h
    · subst h; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (hN t h) (Nat.le_max_right _ _)

/-- `List.tail` is not admissible: admissibility is a genuine restriction in this system. -/
theorem tail_not_admissible : ¬ sys.Adm List.tail := by
  rintro ⟨p, hp⟩
  obtain ⟨L, hL⟩ := run_finite_or_length_le p
  obtain ⟨N, hN⟩ := exists_long L
  let x : Table := (0, 0) :: List.replicate N (0, 0)
  rcases hL x with h | h
  · rw [hp x] at h
    have := hN _ h
    simp [x] at this
  · rw [hp x] at h
    simp [x] at h
    exact Nat.not_succ_le_self N h

/-! ## Checkers and the main result -/

/-- `allOutputsZero` is sound for `IsZeroFn` but not complete. -/
theorem allOutputsZero_sound_not_complete :
    SoundFor allOutputsZero IsZeroFn ∧ ¬ CompleteFor allOutputsZero IsZeroFn := by
  refine ⟨?_, ?_⟩
  · intro t h n
    induction t with
    | nil => rfl
    | cons p t ih =>
      obtain ⟨k, v⟩ := p
      have h' : v = 0 ∧ allOutputsZero t = true := by
        simpa [allOutputsZero] using h
      by_cases hnk : n = k
      · simp [eval, hnk, h'.1]
      · simp only [eval, hnk, ite_false]
        exact ih h'.2
  · intro hc
    have := hc [(0, 0), (0, 5)] (by intro n; cases n <;> simp [eval])
    exact Bool.noConfusion this

/-- **Necessity of the fixpoint principle.** The lookup-table system lacks the fixpoint
principle, and the nontrivial extensional predicate `IsZeroFn` is decided inside it by
`zeroCheck` (itself a program of the test language). -/
theorem tables_no_fixpointPrinciple_and_isZeroFn_decidedInside :
    ¬ FixpointPrinciple sys ∧ Extensional sys IsZeroFn ∧ NontrivialPred IsZeroFn ∧
      Decides zeroCheck IsZeroFn ∧ SwitchAdmissible sys zeroCheck :=
  ⟨not_fixpointPrinciple, isZeroFn_extensional, isZeroFn_nontrivial, zeroCheck_decides,
    zeroCheck_switchAdmissible⟩

end Toy.Rice.Tables
