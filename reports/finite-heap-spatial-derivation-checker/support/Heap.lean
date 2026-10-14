import Std
namespace FiniteHeap
abbrev Heap (n : Nat) := Fin n → Option Nat
instance : DecidableEq (Heap n) := fun h k =>
  if eq : ∀ a, h a = k a then isTrue (funext eq)
  else isFalse (fun same => eq (congrFun same))
def empty : Heap n := fun _ => none
def union (h k : Heap n) : Heap n := fun a => (h a).or (k a)
def Disjoint (h k : Heap n) : Prop := ∀ a, h a = none ∨ k a = none
def Join (h k total : Heap n) : Prop := Disjoint h k ∧ total = union h k
instance (h k : Heap n) : Decidable (Disjoint h k) := inferInstanceAs (Decidable (∀ a, h a = none ∨ k a = none))
instance (h k t : Heap n) : Decidable (Join h k t) := inferInstanceAs (Decidable (Disjoint h k ∧ t = union h k))
theorem join_empty (h : Heap n) : Join h empty h := by
  constructor
  · intro a; exact Or.inr rfl
  · funext a; simp [union, empty]
theorem join_comm {h k t : Heap n} (j : Join h k t) : Join k h t := by
  rcases j with ⟨d, rfl⟩
  constructor
  · intro a; exact (d a).symm
  · funext a
    rcases d a with q | q <;> simp [union, q]
theorem join_assoc {a b ab c abc : Heap n} (j : Join a b ab) (k : Join ab c abc) :
    ∃ bc, Join b c bc ∧ Join a bc abc := by
  rcases j with ⟨d, rfl⟩; rcases k with ⟨e, rfl⟩
  refine ⟨union b c, ⟨?_, rfl⟩, ?_, ?_⟩
  · intro x
    rcases e x with q | q
    · cases ha : a x <;> cases hb : b x <;> simp_all [union]
    · exact Or.inr q
  · intro x
    rcases d x with q | q
    · exact Or.inl q
    · rcases e x with r | r
      · cases ha : a x <;> simp_all [union]
      · exact Or.inr (by simp [union, q, r])
  · funext x; simp [union, Option.or_assoc]
theorem join_cancel {a b c t : Heap n} (j : Join a b t) (k : Join a c t) : b = c := by
  rcases j with ⟨d, jt⟩; rcases k with ⟨e, kt⟩
  funext x
  have same := congrFun (jt.symm.trans kt) x
  cases ax : a x
  · simpa [union, ax] using same
  · have bx : b x = none := (d x).resolve_left (by simp [ax])
    have cx : c x = none := (e x).resolve_left (by simp [ax])
    exact bx.trans cx.symm
abbrev Assertion (n : Nat) := Heap n → Prop
def sep (P Q : Assertion n) : Assertion n := fun h => ∃ p q, Join p q h ∧ P p ∧ Q q
def exactHeap (p : Heap n) : Assertion n := fun h => h = p
def Entails (P Q : Assertion n) : Prop := ∀ h, P h → Q h
theorem sep_comm (P Q : Assertion n) : Entails (sep P Q) (sep Q P) := by
  rintro h ⟨p,q,j,hp,hq⟩; exact ⟨q,p,join_comm j,hq,hp⟩
theorem frame_entail {P Q : Assertion n} (e : Entails P Q) (R : Assertion n) :
    Entails (sep P R) (sep Q R) := by
  rintro h ⟨p,q,j,hp,hq⟩; exact ⟨p,q,j,e p hp,hq⟩
def single (a : Fin n) (v : Nat) : Heap n := fun b => if b = a then some v else none
def write (h : Heap n) (a : Fin n) (v : Nat) : Heap n := fun b => if b = a then some v else h b
theorem write_frame {p f h : Heap n} (a : Fin n) (old new : Nat)
    (j : Join p f h) (owned : p a = some old) : Join (write p a new) f (write h a new) := by
  rcases j with ⟨d, rfl⟩
  have fa : f a = none := (d a).resolve_left (by simp [owned])
  constructor
  · intro b; by_cases eq : b = a
    · exact Or.inr (eq ▸ fa)
    · simpa [write, eq] using d b
  · funext b; by_cases eq : b = a <;> simp [write, union, eq]
def Unchanged (before after : Heap n) (a : Fin n) : Prop := ∀ b, b ≠ a → before b = after b
instance (h k : Heap n) (a : Fin n) : Decidable (Unchanged h k a) := by unfold Unchanged; infer_instance
theorem write_unchanged (h : Heap n) (a : Fin n) (v : Nat) : Unchanged h (write h a v) a := by
  intro b q; simp [write, q]

-- Certificate fields are finite data vectors, not functions or imported proofs.
abbrev Data (n : Nat) := Vector (Option Nat) n
def meaning (d : Data n) : Heap n := fun a => d[a]
structure Step (n : Nat) where
  before : Data n
  after : Data n
  owned : Data n
  frame : Data n
  address : Fin n
  oldValue : Nat
  newValue : Nat
  deriving Repr, DecidableEq
def StepValid (s : Step n) : Prop :=
  Join (meaning s.owned) (meaning s.frame) (meaning s.before) ∧
  meaning s.owned s.address = some s.oldValue ∧
  meaning s.after = write (meaning s.before) s.address s.newValue
instance (s : Step n) : Decidable (StepValid s) := by unfold StepValid; infer_instance
def checkStep (s : Step n) : Bool := decide (StepValid s)
theorem step_sound (s : Step n) (ok : checkStep s = true) :
    Join (write (meaning s.owned) s.address s.newValue) (meaning s.frame) (meaning s.after) ∧
    Unchanged (meaning s.before) (meaning s.after) s.address := by
  have valid : StepValid s := of_decide_eq_true ok
  rcases valid with ⟨j,owned,after⟩
  rw [after]
  exact ⟨write_frame s.address s.oldValue s.newValue j owned,write_unchanged _ _ _⟩

-- Portable rule grammar: split/merge, named two-cell predicate unfolding,
-- framed write, and sequential composition use explicit endpoints.
inductive Cert (n : Nat) where
  | split (left right total : Data n)
  | unfoldPair (a b : Fin n) (x y : Nat) (total : Data n)
  | update (s : Step n)
  | seq (first second : Cert n)
  deriving Repr
def input : Cert n → Heap n
  | .split _ _ total => meaning total
  | .unfoldPair _ _ _ _ total => meaning total
  | .update s => meaning s.before
  | .seq c _ => input c
def output : Cert n → Heap n
  | .split _ _ total => meaning total
  | .unfoldPair _ _ _ _ total => meaning total
  | .update s => meaning s.after
  | .seq _ c => output c
def Valid : Cert n → Prop
  | .split l r t => Join (meaning l) (meaning r) (meaning t)
  | .unfoldPair a b x y t => Join (single a x) (single b y) (meaning t)
  | .update s => StepValid s
  | .seq c d => Valid c ∧ Valid d ∧ output c = input d
def check : Cert n → Bool
  | .split l r t => decide (Join (meaning l) (meaning r) (meaning t))
  | .unfoldPair a b x y t => decide (Join (single a x) (single b y) (meaning t))
  | .update s => checkStep s
  | .seq c d => check c && check d && decide (output c = input d)
theorem check_sound (c : Cert n) (ok : check c = true) : Valid c := by
  induction c with
  | split l r t =>
    change Join (meaning l) (meaning r) (meaning t)
    exact of_decide_eq_true ok
  | unfoldPair a b x y t =>
    change Join (single a x) (single b y) (meaning t)
    exact of_decide_eq_true ok
  | update s =>
    change StepValid s
    exact of_decide_eq_true ok
  | seq c d ihc ihd =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at ok
    exact ⟨ihc ok.1.1,ihd ok.1.2,ok.2⟩
inductive Reach : Heap n → Heap n → Prop where
  | refl (h) : Reach h h
  | update (h : Heap n) (a : Fin n) (old new : Nat) : h a = some old → Reach h (write h a new)
  | trans : Reach h k → Reach k l → Reach h l
theorem valid_reach (c : Cert n) (valid : Valid c) : Reach (input c) (output c) := by
  induction c with
  | split => exact Reach.refl _
  | unfoldPair => exact Reach.refl _
  | update s =>
    rcases valid with ⟨j,owned,after⟩
    have atAddress : meaning s.before s.address = some s.oldValue := by
      rw [j.2]; simp [union,owned]
    rw [output,input,after]; exact Reach.update _ _ _ _ atAddress
  | seq c d ihc ihd =>
    rcases valid with ⟨vc,vd,link⟩
    exact Reach.trans (ihc vc) (link ▸ ihd vd)
theorem certificate_sound (c : Cert n) (ok : check c = true) : Reach (input c) (output c) :=
  valid_reach c (check_sound c ok)
def writesOnly (a : Fin n) : Cert n → Bool
  | .split .. => true
  | .unfoldPair .. => true
  | .update s => decide (s.address = a)
  | .seq c d => writesOnly a c && writesOnly a d
theorem certificate_frame (c : Cert n) (a : Fin n) (ok : check c = true) (only : writesOnly a c = true) :
    Unchanged (input c) (output c) a := by
  have valid := check_sound c ok
  induction c with
  | split => intro b _; rfl
  | unfoldPair => intro b _; rfl
  | update s =>
    have eq : s.address = a := of_decide_eq_true only
    have result := (step_sound s ok).2
    simpa only [eq,input,output] using result
  | seq c d ihc ihd =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at ok
    simp only [writesOnly,Bool.and_eq_true] at only
    have first := ihc ok.1.1 only.1 (check_sound c ok.1.1)
    have second := ihd ok.1.2 only.2 (check_sound d ok.1.2)
    intro b ne
    exact (first b ne).trans ((congrFun ok.2 b).trans (second b ne))
def pairPredicate (a b : Fin n) (x y : Nat) : Assertion n := sep (exactHeap (single a x)) (exactHeap (single b y))
theorem split_assertion {l r t : Heap n} (j : Join l r t) :
    Entails (exactHeap t) (sep (exactHeap l) (exactHeap r)) := by
  rintro h rfl; exact ⟨l,r,j,rfl,rfl⟩
theorem write_single (a : Fin n) (old new : Nat) : write (single a old) a new = single a new := by
  funext b; by_cases eq : b = a <;> simp [write,single,eq]
theorem higher_order_frame (a : Fin n) (old new : Nat) (R : Assertion n) :
    ∀ h, sep (exactHeap (single a old)) R h → sep (exactHeap (single a new)) R (write h a new) := by
  rintro h ⟨p,f,j,rfl,rf⟩
  refine ⟨single a new,f,?_,rfl,rf⟩
  have updated := write_frame a old new j (by simp [single])
  simpa only [write_single] using updated
theorem unfold_pair (a b : Fin n) (x y : Nat) (h : Heap n) :
    pairPredicate a b x y h ↔ Join (single a x) (single b y) h := by
  constructor
  · rintro ⟨p,q,j,rfl,rfl⟩; exact j
  · intro j; exact ⟨_,_,j,rfl,rfl⟩

def data3 (a b c : Option Nat) : Data 3 := #v[a,b,c]
def before := data3 (some 7) (some 11) (some 99)
def after := data3 (some 7) (some 12) (some 99)
def owned := data3 none (some 11) none
def framed := data3 (some 7) none (some 99)
def good : Step 3 := ⟨before,after,owned,framed,1,11,12⟩
def badOverlap : Step 3 := { good with frame := before }
def badFrame : Step 3 := { good with after := data3 (some 8) (some 12) (some 99) }
def badOld : Step 3 := { good with oldValue := 10 }
def badMissing : Step 3 := { good with owned := data3 none none none }
theorem accepted : checkStep good = true := by decide
theorem rejected_overlap : checkStep badOverlap = false := by decide
theorem rejected_frame : checkStep badFrame = false := by decide
theorem rejected_old : checkStep badOld = false := by decide
theorem rejected_missing : checkStep badMissing = false := by decide
theorem checked_same_statement : Join (write (meaning owned) 1 12) (meaning framed) (meaning after) ∧
    Unchanged (meaning before) (meaning after) 1 := step_sound good accepted
theorem direct_same_statement : Join (write (meaning owned) 1 12) (meaning framed) (meaning after) ∧
    Unchanged (meaning before) (meaning after) 1 := by
  constructor <;> decide
def splitGood : Cert 3 := .split owned framed before
def splitOverlap : Cert 3 := .split before before before
def pairGood : Cert 3 := .unfoldPair 0 1 7 11 (data3 (some 7) (some 11) none)
def pairAlias : Cert 3 := .unfoldPair 0 0 7 7 (data3 (some 7) none none)
def goodChain : Cert 3 := .seq splitGood (.update good)
def badChain : Cert 3 := .seq pairGood (.update good)
theorem checked_chain : Reach (input goodChain) (output goodChain) := certificate_sound goodChain (by decide)
theorem no_duplicate_ownership : check splitOverlap = false := by decide
theorem no_aliased_pair : check pairAlias = false := by decide
theorem no_broken_link : check badChain = false := by decide
#print axioms join_assoc
#print axioms certificate_sound
#print axioms certificate_frame
#print axioms higher_order_frame
#print axioms checked_same_statement
#print axioms direct_same_statement
#eval [checkStep good,checkStep badOverlap,checkStep badFrame,checkStep badOld,checkStep badMissing]
#eval [check splitGood,check splitOverlap,check pairGood,check pairAlias,check goodChain,check badChain]
end FiniteHeap
