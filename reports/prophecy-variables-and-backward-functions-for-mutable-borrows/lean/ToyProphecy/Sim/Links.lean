import ToyProphecy.Sim.Clean

/-!
# Proof infrastructure: chains of reborrows

A chain of live borrows is listed top first: the head is the active borrow, every
other element is frozen and is the parent of the element before it.

Auxiliary definitions and lemmas used only inside proofs of the main statements.
-/

namespace Toy.Prophecy
namespace Sim

open CState

/-- `k` is a reborrow of `p`: checker lender link, backward function writing the
final value into `p`, and `p`'s current value in the prophecy translation is
`k`'s prophecy. -/
def LinkAt (c : CState) (sB : BState) (sP : PState) (k p : RefVar) : Prop :=
  c.lender k = some (.ref p) ∧
  (∃ q, sB.refs k = some q ∧ q.back = fun v => [(.ref p, v)]) ∧
  (∃ pk pp, sP.refs k = some pk ∧ sP.refs p = some pp ∧ pp.cur = pk.fin)

def Links (c : CState) (sB : BState) (sP : PState) : List RefVar → Prop
  | [] => True
  | [_] => True
  | k :: p :: rest => LinkAt c sB sP k p ∧ Links c sB sP (p :: rest)

theorem map_eq_some_of {α β : Type} {f : α → β} {o o' : Option α} {x : α}
    (h : o'.map f = o.map f) (hx : o = some x) : ∃ x', o' = some x' ∧ f x' = f x := by
  subst hx
  cases o' with
  | none => simp at h
  | some x' => exact ⟨x', rfl, by simpa using h⟩

theorem linkAt_congr {c c' : CState} {sB sB' : BState} {sP sP' : PState} {k p : RefVar}
    (h : LinkAt c sB sP k p) (hl : c'.lender k = c.lender k)
    (hb : (sB'.refs k).map BRef.back = (sB.refs k).map BRef.back)
    (hf : (sP'.refs k).map PRef.fin = (sP.refs k).map PRef.fin)
    (hc : (sP'.refs p).map PRef.cur = (sP.refs p).map PRef.cur) :
    LinkAt c' sB' sP' k p := by
  obtain ⟨h1, ⟨q, hq, hqb⟩, ⟨pk, pp, hpk, hpp, hcur⟩⟩ := h
  obtain ⟨q', hq', hq'b⟩ := map_eq_some_of hb hq
  obtain ⟨pk', hpk', hpk'f⟩ := map_eq_some_of hf hpk
  obtain ⟨pp', hpp', hpp'c⟩ := map_eq_some_of hc hpp
  exact ⟨hl.trans h1, ⟨q', hq', hq'b.trans hqb⟩, ⟨pk', pp', hpk', hpp', by rw [hpp'c, hpk'f, hcur]⟩⟩

theorem links_congr {c c' : CState} {sB sB' : BState} {sP sP' : PState} :
    ∀ (l : List RefVar), Links c sB sP l →
    (∀ k ∈ l, c'.lender k = c.lender k) →
    (∀ k ∈ l, (sB'.refs k).map BRef.back = (sB.refs k).map BRef.back) →
    (∀ k ∈ l, (sP'.refs k).map PRef.fin = (sP.refs k).map PRef.fin) →
    (∀ k ∈ l.tail, (sP'.refs k).map PRef.cur = (sP.refs k).map PRef.cur) →
    Links c' sB' sP' l
  | [], _, _, _, _, _ => trivial
  | [_], _, _, _, _, _ => trivial
  | k :: p :: rest, ⟨hlk, hrest⟩, hl, hb, hf, hc => by
      refine ⟨linkAt_congr hlk (hl k (by simp)) (hb k (by simp)) (hf k (by simp))
        (hc p (by simp)), ?_⟩
      exact links_congr (p :: rest) hrest (fun j hj => hl j (List.mem_cons_of_mem _ hj))
        (fun j hj => hb j (List.mem_cons_of_mem _ hj)) (fun j hj => hf j (List.mem_cons_of_mem _ hj))
        (fun j hj => hc j (by simp only [List.tail_cons] at hj ⊢; exact List.mem_cons_of_mem _ hj))

theorem links_tail {c : CState} {sB : BState} {sP : PState} {k : RefVar} {l : List RefVar}
    (h : Links c sB sP (k :: l)) : Links c sB sP l := by
  cases l with
  | nil => trivial
  | cons p rest => exact h.2

/-- In a chain, every non-head element is the parent of some element. -/
theorem links_child {c : CState} {sB : BState} {sP : PState} :
    ∀ (l : List RefVar), Links c sB sP l → ∀ j ∈ l.tail,
      ∃ k ∈ l, ∃ pk pj, sP.refs k = some pk ∧ sP.refs j = some pj ∧ pj.cur = pk.fin
  | [], _, j, hj => by simp at hj
  | [_], _, j, hj => by simp at hj
  | k :: p :: rest, ⟨⟨_, _, ⟨pk, pp, hpk, hpp, hcur⟩⟩, hrest⟩, j, hj => by
      simp only [List.tail_cons, List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact ⟨k, by simp, pk, pp, hpk, hpp, hcur⟩
      · obtain ⟨k', hk', h⟩ := links_child (p :: rest) hrest j (by simpa using hj)
        exact ⟨k', List.mem_cons_of_mem _ hk', h⟩

/-! ## Agreement of expression values -/

theorem eval_agree {L : Bool} {c : CState} {sR : RState} {sB : BState} {sP : PState}
    (hd : ∀ k, c.status k = .active → ∃ x, sR.refs k = some x ∧
      (sB.refs k).map BRef.cur = some (sR.store x) ∧ (sP.refs k).map PRef.cur = some (sR.store x))
    (hl : ∀ x, L = true → c.lent x = false → sB.store x = sR.store x ∧ sP.store x = sR.store x) :
    ∀ e, ExprOK L c e → ∃ v, evalR L sR e = some v ∧ evalB L sB e = some v ∧ evalP L sP e = some v
  | .lit n, _ => ⟨n, rfl, rfl, rfl⟩
  | .var x, ⟨hL, hx⟩ => by
      subst hL
      obtain ⟨h1, h2⟩ := hl x rfl hx
      exact ⟨sR.store x, rfl, by simp [evalB, h1], by simp [evalP, h2]⟩
  | .deref r, h => by
      obtain ⟨x, hx, hb, hp⟩ := hd r h
      exact ⟨sR.store x, by simp [evalR, hx], by simpa [evalB] using hb, by simpa [evalP] using hp⟩
  | .add a b, ⟨ha, hb⟩ => by
      obtain ⟨u, hu1, hu2, hu3⟩ := eval_agree hd hl a ha
      obtain ⟨v, hv1, hv2, hv3⟩ := eval_agree hd hl b hb
      exact ⟨u + v, by simp [evalR, hu1, hv1], by simp [evalB, hu2, hv2], by simp [evalP, hu3, hv3]⟩

/-! ## `release` -/

theorem release_ref {c : CState} {r p : RefVar} (hl : c.lender r = some (.ref p))
    (hp : c.status p = .frozen) : c.release r = { c with status := upd c.status p .active } := by
  simp [CState.release, hl, hp]

theorem release_none {c : CState} {r : RefVar} (hl : c.lender r = none) : c.release r = c := by
  simp [CState.release, hl]

end Sim
end Toy.Prophecy
