import HeapCore
open FiniteHeap
namespace ResourceAdapter
-- First-order array/permission schema; hidden values in unowned cells have no meaning.
structure MaskData (n : Nat) where
  values : Vector Nat n
  owns : Vector Bool n
  deriving Repr
def decode (m : MaskData n) : Heap n := fun a => if m.owns[a] then some m.values[a] else none
def encode (d : Data n) : MaskData n := ⟨d.map (fun x => x.getD 0),d.map Option.isSome⟩
theorem roundtrip (d : Data n) : decode (encode d) = meaning d := by
  funext a
  simp only [decode,encode,Vector.getElem_map, Fin.getElem_fin,meaning]
  cases d[a.val] <;> rfl
def compatible (l r : MaskData n) : Prop := ∀ a : Fin n, l.owns[a] = false ∨ r.owns[a] = false
instance (l r : MaskData n) : Decidable (compatible l r) := by unfold compatible; infer_instance
def combine (l r : MaskData n) : MaskData n :=
  ⟨Vector.ofFn (fun a => if l.owns[a] then l.values[a] else r.values[a]),
   Vector.ofFn (fun a => l.owns[a] || r.owns[a])⟩
theorem compatible_decode (l r : MaskData n) (ok : compatible l r) : Disjoint (decode l) (decode r) := by
  intro a; rcases ok a with h | h
  · exact Or.inl (by simp [decode,h])
  · exact Or.inr (by simp [decode,h])
theorem combine_decode (l r : MaskData n) : decode (combine l r) = union (decode l) (decode r) := by
  funext a
  simp only [decode,combine,Vector.getElem_ofFn, Fin.getElem_fin,union]
  cases l.owns[a.val] <;> cases r.owns[a.val] <;> rfl
theorem join_transport (l r : MaskData n) (ok : compatible l r) :
    Join (decode l) (decode r) (decode (combine l r)) :=
  ⟨compatible_decode l r ok,combine_decode l r⟩
def translateAssertion (P : Assertion n) : MaskData n → Prop := fun m => P (decode m)
theorem entailment_transport {P Q : Assertion n} (e : Entails P Q) :
    ∀ m, translateAssertion P m → translateAssertion Q m := fun m hp => e (decode m) hp
theorem encoded_update_transport (s : Step n) (ok : checkStep s = true) :
    Join (write (decode (encode s.owned)) s.address s.newValue) (decode (encode s.frame)) (decode (encode s.after)) ∧
    Unchanged (decode (encode s.before)) (decode (encode s.after)) s.address := by
  simp only [roundtrip];exact step_sound s ok

def noOwn : MaskData 2 := ⟨#v[7,11],#v[false,false]⟩
def left : MaskData 2 := ⟨#v[7,0],#v[true,false]⟩
def right : MaskData 2 := ⟨#v[0,11],#v[false,true]⟩
def duplicate : MaskData 2 := ⟨#v[7,11],#v[true,false]⟩
example : decode noOwn = empty := by
  have q : ∀ a : Fin 2, decode noOwn a = empty a := by decide
  exact funext q
example : compatible left right := by decide
example : ¬compatible left duplicate := by decide
example : Join (decode left) (decode right) (decode (combine left right)) := join_transport _ _ (by decide)
#print axioms roundtrip
#print axioms join_transport
#print axioms entailment_transport
#print axioms encoded_update_transport
#eval [decide (compatible left right),decide (compatible left duplicate)]
end ResourceAdapter
