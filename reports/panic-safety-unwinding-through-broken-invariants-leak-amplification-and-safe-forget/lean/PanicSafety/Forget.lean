import PanicSafety.Characterization

/-!
# Safe leaking: destructors cannot carry soundness

A client language of safe operations over a drain-like API. `drain` hands the client a
guard; `next` moves the next element out to the client as an owned value; dropping the
guard drops the remaining elements and sets `len := 0`. `mem::forget` of a value or of the
guard is a safe operation.

* `destructorReliant`: `drain` leaves `len` unchanged and relies on the guard's destructor
  to fix it.
* `leakAmplified`: `drain` sets `len := 0` immediately.

The closure-scoped alternative (`drainWith`) is a library operation in `Prog`, not in the
client language: the library keeps the guard in its own frame and passes each element by
value to the user callback, which drops it, forgets it, or panics. User code in `Prog` has no
instruction that could reach the library's guard.

Scope of the client language: destructors do not panic, and there is no panic and no
unwinding; ill-typed programs are rejected (`COut.rejected`, a compile error, not UB). The
drain guard's destructor (`dropGuard`, and the guard drop in `cend`) drops the remaining
elements and then sets `len := 0`.
-/

namespace Toy.PanicSafety

/-- The two drain designs. -/
inductive DrainApi where
  | destructorReliant
  | leakAmplified
deriving DecidableEq, Repr

/-- Safe client operations. -/
inductive CInstr where
  /-- Create a drain guard over the whole container (the container is then mutably
  borrowed until the guard is dropped or forgotten). -/
  | drain
  /-- Take the next element out of the guard as a client-owned value (no-op when the
  guard is exhausted). -/
  | next
  /-- Drop the most recently obtained value. -/
  | dropVal
  /-- `mem::forget` the most recently obtained value. -/
  | forgetVal
  /-- Drop the guard (its destructor runs). -/
  | dropGuard
  /-- `mem::forget` the guard. -/
  | forgetGuard
deriving DecidableEq, Repr

/-- Client state: memory, client-owned values (most recent first), and the live guard's
`(cursor, end)` if any. -/
structure CState where
  mem : Mem
  vals : List Tok
  guard : Option (Nat × Nat)
deriving DecidableEq, Repr

/-- Outcome of a client program: completed (after end-of-scope drops), UB, or rejected
(ill-typed: for example `next` without a guard, or `drain` while the container is borrowed;
models a compile error, not UB). -/
inductive COut where
  | ok (s : CState)
  | ub
  | rejected
deriving DecidableEq, Repr

/-- Drop the values in cells `i, i+1, …` (`count` cells) with non-panicking destructors;
`none` is UB. -/
def dropIdxRange (buf : List Cell) : Nat → Nat → List Tok → Option (List Tok)
  | 0, _, d => some d
  | k + 1, i, d =>
    match buf[i]? with
    | some (some t) => if t ∈ d then none else dropIdxRange buf k (i + 1) (t :: d)
    | _ => none

/-- Drop client-owned values in order with non-panicking destructors; `none` is UB. -/
def dropToks : List Tok → List Tok → Option (List Tok)
  | [], d => some d
  | t :: ts, d => if t ∈ d then none else dropToks ts (t :: d)

/-- One client operation. -/
def cstep (api : DrainApi) (s : CState) : CInstr → COut
  | .drain =>
    match s.guard with
    | some _ => .rejected
    | none =>
      .ok { s with guard := some (0, s.mem.len),
                   mem := if api = .leakAmplified then { s.mem with len := 0 } else s.mem }
  | .next =>
    match s.guard with
    | none => .rejected
    | some (c, e) =>
      if c < e then
        match s.mem.buf[c]? with
        | some (some t) => .ok { s with vals := t :: s.vals, guard := some (c + 1, e) }
        | _ => .ub
      else .ok s
  | .dropVal =>
    match s.vals with
    | [] => .rejected
    | t :: vs =>
      if t ∈ s.mem.dropped then .ub
      else .ok { s with vals := vs, mem := { s.mem with dropped := t :: s.mem.dropped } }
  | .forgetVal =>
    match s.vals with
    | [] => .rejected
    | _ :: vs => .ok { s with vals := vs }
  | .dropGuard =>
    match s.guard with
    | none => .rejected
    | some (c, e) =>
      match dropIdxRange s.mem.buf (e - c) c s.mem.dropped with
      | none => .ub
      | some d => .ok { s with guard := none, mem := { s.mem with dropped := d, len := 0 } }
  | .forgetGuard =>
    match s.guard with
    | none => .rejected
    | some _ => .ok { s with guard := none }

/-- End of the client's scope: drop the client's values (most recent first), then the
guard if still live (its destructor runs), then the container. -/
def cend (s : CState) : COut :=
  match dropToks s.vals s.mem.dropped with
  | none => .ub
  | some d1 =>
    let afterGuard : Option (List Tok × Nat) :=
      match s.guard with
      | none => some (d1, s.mem.len)
      | some (c, e) => (dropIdxRange s.mem.buf (e - c) c d1).map fun d => (d, 0)
    match afterGuard with
    | none => .ub
    | some (d2, l) =>
      match containerDrop noPanicDtors { s.mem with dropped := d2, len := l } with
      | .ok d3 => .ok ⟨{ s.mem with dropped := d3, len := l }, [], none⟩
      | _ => .ub

/-- Run a client program from state `s`. -/
def crun (api : DrainApi) : List CInstr → CState → COut
  | [], s => cend s
  | i :: is, s =>
    match cstep api s i with
    | .ok s' => crun api is s'
    | o => o

/-- Run a client program on a container (no values, no guard initially). -/
def clientRun (api : DrainApi) (prog : List CInstr) (m : Mem) : COut :=
  crun api prog ⟨m, [], none⟩

/-- The client of the counterexample: drain, take one value, drop it, forget the guard. -/
def forgetClient : List CInstr := [.drain, .next, .dropVal, .forgetGuard]

/-- Counterexample: with the destructor-reliant drain, the client `forgetClient`, which uses
only safe operations and contains `forgetGuard`, reaches UB on the one-element container
`ceMem1` (the owner's drop drops value `0` a second time). -/
theorem destructorReliantDrain_forget_reachesUB :
    Inv ceMem1 ∧ CInstr.forgetGuard ∈ forgetClient ∧
    clientRun .destructorReliant forgetClient ceMem1 = .ub := by
  decide

/-- The same client against the leak-amplified drain completes without UB (value `0` is
dropped once; nothing is leaked here because the client dropped the only value). -/
theorem leakAmplifiedDrain_forgetClient_ok :
    Inv ceMem1 ∧
    clientRun .leakAmplified forgetClient ceMem1 = .ok ⟨⟨[some 0], 0, [0], 0, 0⟩, [], none⟩ := by
  decide

/-- Without `forgetGuard`, the same steps (with the guard dropped at end of scope) complete
without UB under the destructor-reliant drain. -/
theorem destructorReliantDrain_noForget_example :
    Inv ceMem1 ∧ CInstr.forgetGuard ∉ ([.drain, .next, .dropVal] : List CInstr) ∧
    clientRun .destructorReliant [.drain, .next, .dropVal] ceMem1 =
      .ok ⟨⟨[some 0], 0, [0], 0, 0⟩, [], none⟩ := by
  decide

/-- `forgetVal` is not excluded by the hypothesis of
`destructorReliantDrain_noUB_withoutForgetGuard`: forgetting a value taken out of the drain
leaks that value and completes without UB. -/
theorem destructorReliantDrain_forgetVal_example :
    Inv ceMem1 ∧ CInstr.forgetGuard ∉ ([.drain, .next, .forgetVal] : List CInstr) ∧
    clientRun .destructorReliant [.drain, .next, .forgetVal] ceMem1 =
      .ok ⟨⟨[some 0], 0, [], 0, 0⟩, [], none⟩ := by
  decide

/-- All client programs of length exactly `k`. -/
def allClients : Nat → List (List CInstr)
  | 0 => [[]]
  | k + 1 => (allClients k).flatMap fun p =>
      [.drain :: p, .next :: p, .dropVal :: p, .forgetVal :: p, .dropGuard :: p, .forgetGuard :: p]

/-- Entry states for the client bounded checks: containers of sizes `0..2` from `testMems`. -/
def clientTestMems : List Mem := testMems 0 ++ testMems 1 ++ testMems 2

set_option maxRecDepth 100000 in
/-- Positive control (bounded, fully checked): with the leak-amplified drain, no client
program of length at most `4` reaches UB on the entry states `clientTestMems`. -/
theorem leakAmplifiedDrain_noUB_upTo4 :
    ∀ k ∈ [0, 1, 2, 3, 4], ∀ prog ∈ allClients k, ∀ m ∈ clientTestMems,
      clientRun .leakAmplified prog m ≠ .ub := by
  decide

set_option maxRecDepth 100000 in
/-- Positive control (bounded, fully checked): with the destructor-reliant drain, no client
program of length at most `4` that does not contain `forgetGuard` reaches UB on the entry
states `clientTestMems`. -/
theorem destructorReliantDrain_noUB_withoutForgetGuard_upTo4 :
    ∀ k ∈ [0, 1, 2, 3, 4], ∀ prog ∈ allClients k, ∀ m ∈ clientTestMems,
      CInstr.forgetGuard ∉ prog → clientRun .destructorReliant prog m ≠ .ub := by
  decide

/-- Counterexample (the entry `Inv` cannot be dropped from `leakAmplifiedDrain_noUB` or
`destructorReliantDrain_noUB_withoutForgetGuard`): the empty client program, which contains
no `forgetGuard`, reaches UB at the owner's drop on `dupMem` under both designs. -/
theorem drainClients_need_inv :
    ¬ Inv dupMem ∧ CInstr.forgetGuard ∉ ([] : List CInstr) ∧
    clientRun .leakAmplified [] dupMem = .ub ∧ clientRun .destructorReliant [] dupMem = .ub := by
  decide

/-- `OwnsUniquely` is invariant under permutation of the cells. -/
theorem cl_ownsUniquely_perm {d : List Tok} {l₁ l₂ : List Cell} (hp : l₁.Perm l₂)
    (h : OwnsUniquely d l₁) : OwnsUniquely d l₂ := by
  have htp : (toks l₁).Perm (toks l₂) := hp.filterMap id
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨fun x hx => h1 x (hp.mem_iff.mpr hx), htp.nodup_iff.mp h2,
    fun t ht => h3 t (htp.mem_iff.mpr ht)⟩

/-- `OwnsUniquely` is inherited by sublists. -/
theorem cl_ownsUniquely_sublist {d : List Tok} {l₁ l₂ : List Cell} (hs : l₁.Sublist l₂)
    (h : OwnsUniquely d l₂) : OwnsUniquely d l₁ := by
  have hts : (toks l₁).Sublist (toks l₂) := hs.filterMap id
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨fun x hx => h1 x (hs.subset hx), h2.sublist hts, fun t ht => h3 t (hts.subset ht)⟩

/-- After the values of a prefix `a` join the drop log, the suffix `b` is still uniquely owned. -/
theorem cl_ownsUniquely_append_log {d d' : List Tok} {a b : List Cell}
    (h : OwnsUniquely d (a ++ b)) (hd : ∀ x ∈ d', x ∈ toks a ∨ x ∈ d) : OwnsUniquely d' b := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [toks_append] at h2 h3
  rw [List.nodup_append] at h2
  obtain ⟨_, h2b, h2d⟩ := h2
  refine ⟨fun c hc => h1 c (List.mem_append_right a hc), h2b, ?_⟩
  intro t ht htd
  rcases hd t htd with hta | htd0
  · exact h2d t hta t ht rfl
  · exact h3 t (List.mem_append_right _ ht) htd0

/-- After the values of a suffix `b` join the drop log, the prefix `a` is still uniquely owned. -/
theorem cl_ownsUniquely_append_log_right {d d' : List Tok} {a b : List Cell}
    (h : OwnsUniquely d (a ++ b)) (hd : ∀ x ∈ d', x ∈ toks b ∨ x ∈ d) : OwnsUniquely d' a :=
  cl_ownsUniquely_append_log (cl_ownsUniquely_perm List.perm_append_comm h) hd

/-- The tokens of a list of initialized cells built from tokens are those tokens. -/
theorem cl_toks_map_some (l : List Tok) : toks (l.map some) = l := by
  simp [toks, List.filterMap_map]

/-- `dropToks` succeeds on uniquely owned values, prepending them reversed to the log. -/
theorem cl_dropToks_eq (ts d : List Tok) (h : OwnsUniquely d (ts.map some)) :
    dropToks ts d = some (ts.reverse ++ d) := by
  induction ts generalizing d with
  | nil => rfl
  | cons t ts ih =>
    rw [List.map_cons, ownsUniquely_cons_some_iff] at h
    simp only [dropToks, h.1, ite_false]
    rw [ih _ h.2]
    simp

/-- `dropIdxRange` succeeds on an in-bounds, uniquely owned range of cells, prepending the
range's values reversed to the log. -/
theorem cl_dropIdxRange_eq (buf : List Cell) (k i : Nat) (d : List Tok)
    (hb : i + k ≤ buf.length) (h : OwnsUniquely d ((buf.drop i).take k)) :
    dropIdxRange buf k i d = some ((toks ((buf.drop i).take k)).reverse ++ d) := by
  induction k generalizing i d with
  | zero => simp [dropIdxRange, toks]
  | succ k ih =>
    have hi : i < buf.length := by omega
    have hsplit : (buf.drop i).take (k + 1) = buf[i] :: (buf.drop (i + 1)).take k := by
      rw [List.drop_eq_getElem_cons hi, List.take_succ_cons]
    rw [hsplit] at h ⊢
    have hne : buf[i] ≠ none := h.1 _ List.mem_cons_self
    obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hne
    rw [ht] at h ⊢
    rw [ownsUniquely_cons_some_iff] at h
    have hget : buf[i]? = some (some t) := by rw [List.getElem?_eq_getElem hi, ht]
    simp only [dropIdxRange, hget, h.1, ite_false]
    rw [ih (i + 1) (t :: d) (by omega) h.2, toks_cons_some]
    simp

/-- Dropping uniquely owned cells with non-panicking destructors completes. -/
theorem cl_dropCells_noPanic_ok (cs : List Cell) (d : List Tok) (h : OwnsUniquely d cs) :
    ∃ d', dropCells noPanicDtors cs d = .ok d' := by
  induction cs generalizing d with
  | nil => exact ⟨d, rfl⟩
  | cons c cs ih =>
    have hne : c ≠ none := h.1 _ List.mem_cons_self
    obtain ⟨t, rfl⟩ := Option.ne_none_iff_exists'.mp hne
    rw [ownsUniquely_cons_some_iff] at h
    simp only [dropCells, h.1, ite_false, noPanicDtors, Bool.false_eq_true]
    exact ih _ h.2

/-- Client-state invariant for the drain client language: without a guard the client's values
and the container's elements are uniquely owned; with a guard `(c, e)` the client's values and
the guard's remaining range `[c, e)` are, and under the leak-amplified drain `len = 0`. -/
def DrainClientInv (api : DrainApi) (s : CState) : Prop :=
  match s.guard with
  | none => s.mem.len ≤ s.mem.buf.length ∧
      OwnsUniquely s.mem.dropped (s.vals.map some ++ s.mem.elems)
  | some (c, e) => c ≤ e ∧ e ≤ s.mem.buf.length ∧
      OwnsUniquely s.mem.dropped (s.vals.map some ++ (s.mem.buf.drop c).take (e - c)) ∧
      (api = .leakAmplified → s.mem.len = 0)

/-- The end-of-scope drops never reach UB from a state satisfying `DrainClientInv`. -/
theorem cl_cend_ne_ub (api : DrainApi) (s : CState) (hs : DrainClientInv api s) :
    cend s ≠ .ub := by
  obtain ⟨⟨buf, len, d, ca, cb⟩, vals, guard⟩ := s
  have hV : ∀ R, OwnsUniquely d (vals.map some ++ R) →
      dropToks vals d = some (vals.reverse ++ d) := fun R h =>
    cl_dropToks_eq _ _ (cl_ownsUniquely_sublist (List.sublist_append_left _ _) h)
  have hlog : ∀ x ∈ vals.reverse ++ d, x ∈ toks (vals.map some) ∨ x ∈ d := by
    intro x hx
    rw [cl_toks_map_some]
    simpa using hx
  cases guard with
  | none =>
    obtain ⟨hlen, hown⟩ := hs
    have hE : OwnsUniquely (vals.reverse ++ d) (buf.take len) :=
      cl_ownsUniquely_append_log hown hlog
    obtain ⟨d3, hd3⟩ := cl_dropCells_noPanic_ok _ _ hE
    simp only [cend, hV _ hown, containerDrop, Mem.elems, hlen, ite_true, hd3]
    simp
  | some ce =>
    obtain ⟨c, e⟩ := ce
    obtain ⟨hce, he, hown, _⟩ := hs
    have he' : e ≤ buf.length := he
    have hR : OwnsUniquely (vals.reverse ++ d) ((buf.drop c).take (e - c)) :=
      cl_ownsUniquely_append_log hown hlog
    have hdr := cl_dropIdxRange_eq buf (e - c) c _ (by omega) hR
    simp only [cend, hV _ hown, hdr, Option.map_some, containerDrop, Mem.elems,
      Nat.zero_le, ite_true, List.take_zero, dropCells]
    simp

/-- One client step from a state satisfying `DrainClientInv` is rejected or yields a state
satisfying `DrainClientInv` (never UB), unless it is `forgetGuard` under the destructor-reliant
drain. -/
theorem cl_cstep_ok (api : DrainApi) (s : CState) (i : CInstr) (hs : DrainClientInv api s)
    (hf : api = .destructorReliant → i ≠ .forgetGuard) :
    cstep api s i = .rejected ∨ ∃ s', cstep api s i = .ok s' ∧ DrainClientInv api s' := by
  obtain ⟨⟨buf, len, d, ca, cb⟩, vals, guard⟩ := s
  cases i with
  | drain =>
    cases guard with
    | some ce => exact Or.inl rfl
    | none =>
      obtain ⟨hlen, hown⟩ := hs
      have hlen' : len ≤ buf.length := hlen
      have hown' : OwnsUniquely d (vals.map some ++ buf.take len) := hown
      right
      cases api with
      | destructorReliant =>
        refine ⟨⟨⟨buf, len, d, ca, cb⟩, vals, some (0, len)⟩, ?_, ?_⟩
        · simp [cstep]
        · simp only [DrainClientInv, List.drop_zero, Nat.sub_zero]
          exact ⟨Nat.zero_le _, hlen', hown', by intro h; cases h⟩
      | leakAmplified =>
        refine ⟨⟨⟨buf, 0, d, ca, cb⟩, vals, some (0, len)⟩, ?_, ?_⟩
        · simp [cstep]
        · simp only [DrainClientInv, List.drop_zero, Nat.sub_zero]
          exact ⟨Nat.zero_le _, hlen', hown', by simp⟩
  | next =>
    cases guard with
    | none => exact Or.inl rfl
    | some ce =>
      obtain ⟨c, e⟩ := ce
      obtain ⟨hce, he, hown, hl⟩ := hs
      have he' : e ≤ buf.length := he
      have hown' : OwnsUniquely d (vals.map some ++ (buf.drop c).take (e - c)) := hown
      right
      by_cases hc : c < e
      · have hi : c < buf.length := by omega
        have hsplit : (buf.drop c).take (e - c) =
            buf[c] :: (buf.drop (c + 1)).take (e - (c + 1)) := by
          have h1 : e - c = (e - (c + 1)) + 1 := by omega
          rw [h1, List.drop_eq_getElem_cons hi, List.take_succ_cons]
        rw [hsplit] at hown'
        have hne : buf[c] ≠ none := hown'.1 _ (List.mem_append_right _ List.mem_cons_self)
        obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hne
        rw [ht] at hown'
        have hget : buf[c]? = some (some t) := by rw [List.getElem?_eq_getElem hi, ht]
        refine ⟨⟨⟨buf, len, d, ca, cb⟩, t :: vals, some (c + 1, e)⟩, ?_, ?_⟩
        · simp [cstep, hc, hget]
        · simp only [DrainClientInv]
          refine ⟨by omega, he', ?_, hl⟩
          rw [List.map_cons, List.cons_append]
          exact cl_ownsUniquely_perm List.perm_middle hown'
      · refine ⟨⟨⟨buf, len, d, ca, cb⟩, vals, some (c, e)⟩, ?_, ?_⟩
        · simp [cstep, hc]
        · exact ⟨hce, he, hown, hl⟩
  | dropVal =>
    cases vals with
    | nil => exact Or.inl rfl
    | cons t vs =>
      right
      have key : ∀ X, OwnsUniquely d ((t :: vs).map some ++ X) →
          t ∉ d ∧ OwnsUniquely (t :: d) (vs.map some ++ X) := by
        intro X h
        rw [List.map_cons, List.cons_append, ownsUniquely_cons_some_iff] at h
        exact h
      cases guard with
      | none =>
        obtain ⟨hlen, hown⟩ := hs
        obtain ⟨htd, hown'⟩ := key _ hown
        refine ⟨⟨⟨buf, len, t :: d, ca, cb⟩, vs, none⟩, ?_, ?_⟩
        · simp [cstep, htd]
        · exact ⟨hlen, hown'⟩
      | some ce =>
        obtain ⟨c, e⟩ := ce
        obtain ⟨hce, he, hown, hl⟩ := hs
        obtain ⟨htd, hown'⟩ := key _ hown
        refine ⟨⟨⟨buf, len, t :: d, ca, cb⟩, vs, some (c, e)⟩, ?_, ?_⟩
        · simp [cstep, htd]
        · exact ⟨hce, he, hown', hl⟩
  | forgetVal =>
    cases vals with
    | nil => exact Or.inl rfl
    | cons t vs =>
      right
      have key : ∀ X, OwnsUniquely d ((t :: vs).map some ++ X) →
          OwnsUniquely d (vs.map some ++ X) := by
        intro X h
        rw [List.map_cons, List.cons_append] at h
        exact cl_ownsUniquely_sublist (List.sublist_cons_self _ _) h
      cases guard with
      | none =>
        obtain ⟨hlen, hown⟩ := hs
        refine ⟨⟨⟨buf, len, d, ca, cb⟩, vs, none⟩, ?_, ?_⟩
        · simp [cstep]
        · exact ⟨hlen, key _ hown⟩
      | some ce =>
        obtain ⟨c, e⟩ := ce
        obtain ⟨hce, he, hown, hl⟩ := hs
        refine ⟨⟨⟨buf, len, d, ca, cb⟩, vs, some (c, e)⟩, ?_, ?_⟩
        · simp [cstep]
        · exact ⟨hce, he, key _ hown, hl⟩
  | dropGuard =>
    cases guard with
    | none => exact Or.inl rfl
    | some ce =>
      obtain ⟨c, e⟩ := ce
      obtain ⟨hce, he, hown, hl⟩ := hs
      have he' : e ≤ buf.length := he
      have hown' : OwnsUniquely d (vals.map some ++ (buf.drop c).take (e - c)) := hown
      have hR : OwnsUniquely d ((buf.drop c).take (e - c)) :=
        cl_ownsUniquely_sublist (List.sublist_append_right _ _) hown'
      have hdr := cl_dropIdxRange_eq buf (e - c) c d (by omega) hR
      right
      refine ⟨⟨⟨buf, 0, (toks ((buf.drop c).take (e - c))).reverse ++ d, ca, cb⟩, vals, none⟩,
        ?_, ?_⟩
      · simp [cstep, hdr]
      · simp only [DrainClientInv, Mem.elems, List.take_zero, List.append_nil]
        refine ⟨Nat.zero_le _, cl_ownsUniquely_append_log_right hown' ?_⟩
        intro x hx
        simpa using hx
  | forgetGuard =>
    cases guard with
    | none => exact Or.inl rfl
    | some ce =>
      obtain ⟨c, e⟩ := ce
      obtain ⟨hce, he, hown, hl⟩ := hs
      have hown' : OwnsUniquely d (vals.map some ++ (buf.drop c).take (e - c)) := hown
      cases api with
      | destructorReliant => exact absurd rfl (hf rfl)
      | leakAmplified =>
        have hl0 : len = 0 := hl rfl
        subst hl0
        right
        refine ⟨⟨⟨buf, 0, d, ca, cb⟩, vals, none⟩, ?_, ?_⟩
        · simp [cstep]
        · simp only [DrainClientInv, Mem.elems, List.take_zero, List.append_nil]
          exact ⟨Nat.zero_le _, cl_ownsUniquely_sublist (List.sublist_append_left _ _) hown'⟩

/-- A client program run from a state satisfying `DrainClientInv` never reaches UB, provided it
contains no `forgetGuard` when the drain is destructor-reliant. -/
theorem cl_crun_ne_ub (api : DrainApi) (is : List CInstr) (s : CState)
    (hs : DrainClientInv api s) (hf : api = .destructorReliant → CInstr.forgetGuard ∉ is) :
    crun api is s ≠ .ub := by
  induction is generalizing s with
  | nil => exact cl_cend_ne_ub api s hs
  | cons i is ih =>
    have hfi : api = .destructorReliant → i ≠ .forgetGuard := fun h heq =>
      hf h (heq ▸ List.mem_cons_self)
    have hfis : api = .destructorReliant → CInstr.forgetGuard ∉ is := fun h hm =>
      hf h (List.mem_cons_of_mem _ hm)
    rcases cl_cstep_ok api s i hs hfi with hr | ⟨s', hs', hinv⟩
    · simp [crun, hr]
    · simp only [crun, hs']
      exact ih s' hinv hfis

/-- The initial client state over a container satisfying `Inv` satisfies `DrainClientInv`. -/
theorem cl_clientInv_init (api : DrainApi) (m : Mem) (hm : Inv m) :
    DrainClientInv api ⟨m, [], none⟩ := by
  obtain ⟨hlen, hown⟩ := hm
  show m.len ≤ m.buf.length ∧ OwnsUniquely m.dropped (([] : List Tok).map some ++ m.elems)
  exact ⟨hlen, by simpa using hown⟩

/-- With the leak-amplified drain, no client program reaches UB from an entry state
satisfying `Inv`. -/
theorem leakAmplifiedDrain_noUB (prog : List CInstr) (m : Mem) (hm : Inv m) :
    clientRun .leakAmplified prog m ≠ .ub :=
  cl_crun_ne_ub _ _ _ (cl_clientInv_init _ m hm) (by intro h; cases h)

/-- With the destructor-reliant drain, no client program that does not contain
`forgetGuard` reaches UB from an entry state satisfying `Inv`. (`forgetVal` is allowed.) -/
theorem destructorReliantDrain_noUB_withoutForgetGuard (prog : List CInstr) (m : Mem) (hm : Inv m)
    (hforget : CInstr.forgetGuard ∉ prog) :
    clientRun .destructorReliant prog m ≠ .ub :=
  cl_crun_ne_ub _ _ _ (cl_clientInv_init _ m hm) (fun _ => hforget)

/-! ## Closure-scoped drain -/

/-- A guard that moves the unprocessed cells `[c, n)` to the front and sets `len := n - c`
(truncated subtraction; the loop keeps `c ≤ n`). -/
def tailFix (c n : Nat) : Guard := ⟨fun b _ => (copyRange (n - c) b c 0, n - c)⟩

/-- Closure-scoped drain loop: mark element `c` processed in the guard, move it out to a
local, and pass it to the user callback, which drops it (`true`) or forgets it (`false`),
or panics while owning it. -/
def drainWithLoop (n : Nat) : Nat → Nat → Prog
  | 0, _ => .popGuard .done
  | r + 1, c => .setGuard (tailFix (c + 1) n) (.readOut c (.call fun dropIt =>
      if dropIt then .dropVal (drainWithLoop n r (c + 1))
      else .forgetVal (drainWithLoop n r (c + 1))))

/-- Closure-scoped drain: the guard lives in the library's frame and is never handed to user
code. The container's `len` is not changed before the loop. -/
def drainWith : Prog := .getLen fun n => .pushGuard (tailFix 0 n) (drainWithLoop n n 0)

/-- `copyRange` preserves the buffer length. -/
theorem dw_copyRange_length (k : Nat) (b : List Cell) (s d : Nat) :
    (copyRange k b s d).length = b.length := by
  induction k generalizing b s d with
  | zero => rfl
  | succ k ih => simp only [copyRange, ih, List.length_set]

/-- `copyRange` leaves the cells below the destination start unchanged. -/
theorem dw_copyRange_getElem?_below (k : Nat) (b : List Cell) (s d i : Nat) (hi : i < d) :
    (copyRange k b s d)[i]? = b[i]? := by
  induction k generalizing b s d with
  | zero => rfl
  | succ k ih =>
    simp only [copyRange]
    rw [ih _ _ _ (by omega), List.getElem?_set_ne (by omega)]

/-- Front-to-back `copyRange` is a correct memmove when `dst ≤ src`: cell `d + i` of the
result holds the original cell `s + i`. -/
theorem dw_copyRange_getElem?_shift (k : Nat) (b : List Cell) (s d : Nat) (hds : d ≤ s)
    (hk : s + k ≤ b.length) (i : Nat) (hi : i < k) :
    (copyRange k b s d)[d + i]? = b[s + i]? := by
  induction k generalizing b s d i with
  | zero => omega
  | succ k ih =>
    simp only [copyRange]
    cases i with
    | zero =>
      have hs : s < b.length := by omega
      show (copyRange k (b.set d (b.getD s none)) (s + 1) (d + 1))[d]? = b[s]?
      rw [dw_copyRange_getElem?_below _ _ _ _ _ (by omega),
        List.getElem?_set_self (by omega), List.getElem?_eq_getElem hs]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]
    | succ i =>
      have := ih (b.set d (b.getD s none)) (s + 1) (d + 1) (by omega)
        (by simp only [List.length_set]; omega) i (by omega)
      rw [show d + (i + 1) = d + 1 + i by omega, this, List.getElem?_set_ne (by omega)]
      congr 1
      omega

/-- The first `n - c` cells after moving `[c, n)` to the front are the cells `[c, n)`. -/
theorem dw_copyRange_take (b : List Cell) (c n : Nat) (hcn : c ≤ n) (hn : n ≤ b.length) :
    (copyRange (n - c) b c 0).take (n - c) = (b.drop c).take (n - c) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, List.getElem?_take]
  split
  · rw [List.getElem?_drop, ← dw_copyRange_getElem?_shift (n - c) b c 0 (Nat.zero_le _)
      (by omega) i ‹_›, Nat.zero_add]
  · rfl

/-- Under `Inv m`, if every value in `D` lies among the first `c` cells, the cells `[c, len)`
are uniquely owned with respect to the extended drop log `D ++ m.dropped`. -/
theorem dw_owns_tail (m : Mem) (hm : Inv m) (c : Nat) (hc : c ≤ m.len) (D : List Tok)
    (hD : ∀ t ∈ D, t ∈ toks (m.buf.take c)) :
    OwnsUniquely (D ++ m.dropped) ((m.buf.drop c).take (m.len - c)) := by
  obtain ⟨_, hinit, hnd, hd⟩ := hm
  have hsplit : m.elems = m.buf.take c ++ (m.buf.drop c).take (m.len - c) := by
    simp only [Mem.elems]
    rw [← List.take_add]
    congr 1
    omega
  rw [hsplit] at hinit hnd hd
  rw [toks_append] at hnd hd
  refine ⟨fun x hx => hinit x (List.mem_append_right _ hx), (List.nodup_append.mp hnd).2.1, ?_⟩
  intro t ht htD
  rcases List.mem_append.mp htD with h | h
  · exact (List.nodup_append.mp hnd).2.2 t (hD t h) t ht rfl
  · exact hd t (List.mem_append_right _ ht) h

/-- Applying the guard `tailFix c len` to the original buffer, with drop log `D ++ m.dropped`
where `D` lies among the first `c` cells, yields a state satisfying `Inv`. -/
theorem dw_inv_fix (m : Mem) (hm : Inv m) (c : Nat) (hc : c ≤ m.len) (D : List Tok)
    (hD : ∀ t ∈ D, t ∈ toks (m.buf.take c)) (x : Mem)
    (hbuf : x.buf = copyRange (m.len - c) m.buf c 0) (hlen : x.len = m.len - c)
    (hdrop : x.dropped = D ++ m.dropped) : Inv x := by
  have hmlen : m.len ≤ m.buf.length := hm.1
  refine ⟨?_, ?_⟩
  · rw [hbuf, hlen, dw_copyRange_length]
    omega
  · simp only [Mem.elems]
    rw [hbuf, hlen, hdrop, dw_copyRange_take _ _ _ hc hmlen]
    exact dw_owns_tail m hm c hc D hD

/-- Under `Inv m`, cell `c < len` holds a value `t` not in `D ++ m.dropped`, and `t :: D`
lies among the first `c + 1` cells. -/
theorem dw_cell (m : Mem) (hm : Inv m) (c : Nat) (hc : c < m.len) (D : List Tok)
    (hD : ∀ t ∈ D, t ∈ toks (m.buf.take c)) :
    ∃ t, m.buf[c]? = some (some t) ∧ t ∉ D ++ m.dropped ∧
      ∀ u ∈ t :: D, u ∈ toks (m.buf.take (c + 1)) := by
  have hlen : m.len ≤ m.buf.length := hm.1
  have hown := dw_owns_tail m hm c (by omega) D hD
  have hcl : c < m.buf.length := by omega
  rw [List.drop_eq_getElem_cons hcl, show m.len - c = (m.len - c - 1) + 1 by omega,
    List.take_succ_cons] at hown
  have hsome : m.buf[c] ≠ none := hown.1 _ List.mem_cons_self
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hsome
  rw [ht, ownsUniquely_cons_some_iff] at hown
  refine ⟨t, by rw [List.getElem?_eq_getElem hcl, ht], hown.1, ?_⟩
  have htake : m.buf.take (c + 1) = m.buf.take c ++ [some t] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hcl, ht]
    rfl
  intro u hu
  rw [htake, toks_append]
  rcases List.mem_cons.mp hu with rfl | hu
  · exact List.mem_append_right _ (by simp [toks])
  · exact List.mem_append_left _ (hD u hu)

/-- The drain loop at cursor `c` (with `c + r = len`), entered with guard `tailFix c len`,
the original buffer and `len`, and a drop log extended only by values among the first `c`
cells, has an acceptable outcome. -/
theorem dw_loop (cb : Callback) (dt : DtorTable) (m : Mem) (hm : Inv m) :
    ∀ (r c j : Nat) (m' : Mem) (D : List Tok), c + r = m.len → m'.buf = m.buf →
      m'.len = m.len → m'.dropped = D ++ m.dropped →
      (∀ t ∈ D, t ∈ toks (m.buf.take c)) →
      ResOk (exec .unwind cb dt (drainWithLoop m.len r c) j [.guard (tailFix c m.len)] m').1 := by
  intro r
  induction r with
  | zero =>
    intro c j m' D hcr hbuf hlen hdrop hD
    simp only [drainWithLoop, exec, List.isEmpty_nil, ite_true, ResOk]
    exact dw_inv_fix m hm c (by omega) D hD _ (by simp [tailFix, hbuf, hlen])
      (by simp [tailFix, hlen]) hdrop
  | succ r ih =>
    intro c j m' D hcr hbuf hlen hdrop hD
    obtain ⟨t, ht, htD, hD'⟩ := dw_cell m hm c (by omega) D hD
    have ht' : m'.buf[c]? = some (some t) := by rw [hbuf]; exact ht
    have htd : t ∉ m'.dropped := by rw [hdrop]; exact htD
    simp only [drainWithLoop, exec, ht']
    have hc1 : c + 1 ≤ m.len := by omega
    have hD0 : ∀ u ∈ D, u ∈ toks (m.buf.take (c + 1)) := fun u hu => hD' u (List.mem_cons_of_mem _ hu)
    cases hcb : cb j with
    | panic =>
      simp only [panicFrom, unwindEntries, htd, ite_false]
      cases hdt : dt t
      · simp only [Bool.false_eq_true, ite_false, ResOk]
        exact dw_inv_fix m hm (c + 1) hc1 (t :: D) hD' _ (by simp [tailFix, hbuf])
          (by simp [tailFix]) (by simp [hdrop])
      · simp [ResOk]
    | ret b =>
      cases b
      · simp only [Bool.false_eq_true, ite_false, exec]
        exact ih (c + 1) (j + 1) m' D (by omega) hbuf hlen hdrop hD0
      · simp only [ite_true, exec, htd, ite_false]
        cases hdt : dt t
        · simp only [Bool.false_eq_true, ite_false]
          exact ih (c + 1) (j + 1) _ (t :: D) (by omega) hbuf hlen (by simp [hdrop]) hD'
        · simp only [ite_true, panicFrom, unwindEntries, ResOk]
          exact dw_inv_fix m hm (c + 1) hc1 (t :: D) hD' _ (by simp [tailFix, hbuf])
            (by simp [tailFix]) (by simp [hdrop])

/-- The closure-scoped drain is panic-safe under `unwind`: for every callback table
(including callbacks that forget the values they receive or panic while owning one), every
destructor table, and every entry state satisfying `Inv`, the run reaches no UB and a return
or an unwind leaves `Inv`. -/
theorem closureScopedDrain_panicSafe_unwind : PanicSafe .unwind drainWith := by
  intro cb dt m hm
  simp only [run, drainWith, exec]
  exact dw_loop cb dt m hm m.len 0 0 m [] (by omega) rfl rfl rfl (by simp)

/-- Bounded check of `closureScopedDrain_panicSafe_unwind` (same family as
`rawRetain_abort_exact_upTo3`). -/
theorem closureScopedDrain_panicSafe_unwind_upTo3 :
    ∀ n ∈ [0, 1, 2, 3], ∀ m ∈ testMems n, ∀ bs ∈ allBehs n, ∀ ds ∈ allBools n,
      ResOk (run .unwind (tableOf bs) (dtOf ds) drainWith m) := by
  decide

/-- Non-vacuity witness: the callback forgets element `0` and panics while owning element
`1`; the run unwinds to a container holding the unprocessed element `2`, with `1` dropped
and `0` leaked. -/
theorem closureScopedDrain_example :
    Inv ceMem3 ∧
    run .unwind (tableOf [.ret false, .panic]) noPanicDtors drainWith ceMem3 =
      .unwound ⟨[some 2, some 1, some 2], 1, [1], 0, 0⟩ ∧
    Inv ⟨[some 2, some 1, some 2], 1, [1], 0, 0⟩ := by
  decide

/-- Counterexample (the entry `Inv` cannot be dropped from
`closureScopedDrain_panicSafe_unwind`): from `dupMem` a panic at the first element unwinds to
a state violating `Inv`; from a one-cell container whose cell is uninitialized the run
reaches UB. -/
theorem drainWith_needs_inv :
    (¬ Inv dupMem ∧ ¬ ResOk (run .unwind (tableOf [.panic]) noPanicDtors drainWith dupMem)) ∧
    (¬ Inv ⟨[none], 1, [], 0, 0⟩ ∧
      run .unwind (tableOf []) noPanicDtors drainWith ⟨[none], 1, [], 0, 0⟩ = .ub) := by
  decide

end Toy.PanicSafety
