module
import all CheckerMain
#print axioms ArithmeticPrototype.posthoc_sound
#print axioms NativeChecker.validate_sound
#print axioms NativeChecker.selected_accepted
#print axioms NativeChecker.wrong_op_rejected
#print axioms NativeChecker.wrong_literal_rejected
example : ∀ x : ArithmeticPrototype.Byte,
 ArithmeticPrototype.evalIR NativeChecker.selectedIR x =
 ArithmeticPrototype.evalSource NativeChecker.selectedSource x :=
 NativeChecker.validate_sound _ NativeChecker.selected_accepted
