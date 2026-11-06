import Lean
namespace ArithmeticPrototype
abbrev Byte := Fin 256
def add8 (a b : Byte) : Byte := ⟨(a.val + b.val) % 256, Nat.mod_lt _ (by decide)⟩
def mul8 (a b : Byte) : Byte := ⟨(a.val * b.val) % 256, Nat.mod_lt _ (by decide)⟩
inductive Source where
 | input
 | literal (v : Byte)
 | wrappingAdd (a b : Source)
 | wrappingMul (a b : Source)
 deriving DecidableEq, Repr
inductive IR where
 | parameter
 | immediate (v : Byte)
 | addByte (a b : IR)
 | mulByte (a b : IR)
 deriving DecidableEq, Repr
def evalSource : Source → Byte → Byte
 | .input, x => x
 | .literal v, _ => v
 | .wrappingAdd a b, x => add8 (evalSource a x) (evalSource b x)
 | .wrappingMul a b, x => mul8 (evalSource a x) (evalSource b x)
def evalIR : IR → Byte → Byte
 | .parameter, x => x
 | .immediate v, _ => v
 | .addByte a b, x => add8 (evalIR a x) (evalIR b x)
 | .mulByte a b, x => mul8 (evalIR a x) (evalIR b x)
def decode : IR → Source
 | .parameter => .input
 | .immediate v => .literal v
 | .addByte a b => .wrappingAdd (decode a) (decode b)
 | .mulByte a b => .wrappingMul (decode a) (decode b)
def construct : Source → IR
 | .input => .parameter
 | .literal v => .immediate v
 | .wrappingAdd a b => .addByte (construct a) (construct b)
 | .wrappingMul a b => .mulByte (construct a) (construct b)
theorem decode_eval (p : IR) (x : Byte) : evalSource (decode p) x = evalIR p x := by
 induction p with
 | parameter => rfl
 | immediate => rfl
 | addByte a b ha hb => simp only [decode, evalSource, evalIR, ha, hb]
 | mulByte a b ha hb => simp only [decode, evalSource, evalIR, ha, hb]
theorem construct_eval (s : Source) (x : Byte) :
 evalIR (construct s) x = evalSource s x := by
 induction s with
 | input => rfl
 | literal => rfl
 | wrappingAdd a b ha hb => simp only [construct, evalIR, evalSource, ha, hb]
 | wrappingMul a b ha hb => simp only [construct, evalIR, evalSource, ha, hb]
def checkPosthoc (s : Source) (p : IR) : Bool := decide (decode p = s)
theorem posthoc_sound (s : Source) (p : IR) (h : checkPosthoc s p = true) :
 ∀ x, evalIR p x = evalSource s x := by
 have same : decode p = s := of_decide_eq_true h
 intro x
 rw [← decode_eval, same]
structure Row where
 input : Nat
 a : Byte
 b : Byte
 output : Byte
 deriving Repr
instance : Inhabited Row := ⟨⟨0, 0, 0, 0⟩⟩
def intermediateA (x : Byte) := add8 x ⟨3, by decide⟩
def intermediateB (x : Byte) := mul8 (intermediateA x) ⟨5, by decide⟩
def checkInstrumented (s : Source) (p : IR) (rows : Array Row) : Bool :=
 decide (rows.size = 256) &&
 decide (∀ x : Byte,
   (rows[x.val]!).input = x.val ∧
   (rows[x.val]!).a = intermediateA x ∧
   (rows[x.val]!).b = intermediateB x ∧
   (rows[x.val]!).output = evalSource s x ∧
   (rows[x.val]!).output = evalIR p x)
theorem instrumented_sound (s : Source) (p : IR) (rows : Array Row)
 (h : checkInstrumented s p rows = true) : ∀ x, evalIR p x = evalSource s x := by
 have hs : (decide (∀ x : Byte,
   (rows[x.val]!).input = x.val ∧
   (rows[x.val]!).a = intermediateA x ∧
   (rows[x.val]!).b = intermediateB x ∧
   (rows[x.val]!).output = evalSource s x ∧
   (rows[x.val]!).output = evalIR p x)) = true := by
  have h' := h
  simp only [checkInstrumented, Bool.and_eq_true_iff] at h'
  exact h'.2
 have all := of_decide_eq_true hs
 intro x
 exact (all x).2.2.2.2.symm.trans (all x).2.2.2.1
def Claim (expected actual : String) (s : Source) (p : IR) : Prop :=
 expected = actual ∧ ∀ x : Byte, evalIR p x = evalSource s x
end ArithmeticPrototype


open ArithmeticPrototype
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
def expectedSourceHash : String := "e3a37308bc49b9ed0308dbcbc6e63890b74a22de29abdf7030673b7ad6c642e8"
def actualSourceHash : String := "e3a37308bc49b9ed0308dbcbc6e63890b74a22de29abdf7030673b7ad6c642e8"
def capturedSource : Source := .wrappingAdd (.wrappingMul (.wrappingAdd (.input) (.literal 3)) (.literal 5)) (.literal 7)
def proposedIR : IR := .addByte (.mulByte (.addByte (.parameter) (.immediate 3)) (.immediate 5)) (.immediate 7)
theorem acceptance : checkPosthoc capturedSource proposedIR = true := by decide +kernel
theorem consumerAccepted : Claim expectedSourceHash actualSourceHash capturedSource proposedIR := False.elim (by decide)
#print axioms consumerAccepted
