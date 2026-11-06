module
import all CheckerMain
theorem selectedInput : NativeChecker.validate NativeChecker.selectedIR = true := by decide
#print axioms selectedInput
