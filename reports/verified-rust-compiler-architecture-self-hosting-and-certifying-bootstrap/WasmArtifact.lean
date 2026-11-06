import WasmValidator
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
open RestrictedWasm
def actualBytes : List Nat := [0, 97, 115, 109, 1, 0, 0, 0, 1, 9, 1, 96, 4, 127, 127, 127, 127, 1, 127, 3, 2, 1, 0, 7, 12, 1, 8, 118, 97, 108, 105, 100, 97, 116, 101, 0, 0, 10, 27, 1, 25, 0, 32, 0, 65, 2, 73, 32, 1, 65, 2, 73, 113, 32, 2, 65, 2, 73, 32, 3, 65, 2, 73, 113, 113, 11]
theorem actual_admitted : admitFour actualBytes = true := by decide
theorem actual_correct (xs : Inputs) : actualBytes = moduleBytes ∧ run xs (compile four) [] = some [bit (validity xs)] := admit_sound actualBytes actual_admitted xs
theorem changed_constant_rejected : admitFour [0, 97, 115, 109, 1, 0, 0, 0, 1, 9, 1, 96, 4, 127, 127, 127, 127, 1, 127, 3, 2, 1, 0, 7, 12, 1, 8, 118, 97, 108, 105, 100, 97, 116, 101, 0, 0, 10, 27, 1, 25, 0, 32, 0, 65, 64, 73, 32, 1, 65, 2, 73, 113, 32, 2, 65, 2, 73, 32, 3, 65, 2, 73, 113, 113, 11] = false := by decide
theorem changed_predicate_rejected : admitFour [0, 97, 115, 109, 1, 0, 0, 0, 1, 9, 1, 96, 4, 127, 127, 127, 127, 1, 127, 3, 2, 1, 0, 7, 12, 1, 8, 118, 97, 108, 105, 100, 97, 116, 101, 0, 0, 10, 27, 1, 25, 0, 32, 0, 65, 3, 73, 32, 1, 65, 2, 73, 113, 32, 2, 65, 2, 73, 32, 3, 65, 2, 73, 113, 113, 11] = false := by decide
theorem changed_opcode_rejected : admitFour [0, 97, 115, 109, 1, 0, 0, 0, 1, 9, 1, 96, 4, 127, 127, 127, 127, 1, 127, 3, 2, 1, 0, 7, 12, 1, 8, 118, 97, 108, 105, 100, 97, 116, 101, 0, 0, 10, 27, 1, 25, 0, 32, 0, 65, 2, 72, 32, 1, 65, 2, 73, 113, 32, 2, 65, 2, 73, 32, 3, 65, 2, 73, 113, 113, 11] = false := by decide
theorem unknown_opcode_rejected : admitFour [0, 97, 115, 109, 1, 0, 0, 0, 1, 9, 1, 96, 4, 127, 127, 127, 127, 1, 127, 3, 2, 1, 0, 7, 12, 1, 8, 118, 97, 108, 105, 100, 97, 116, 101, 0, 0, 10, 27, 1, 25, 0, 32, 0, 65, 2, 255, 32, 1, 65, 2, 73, 113, 32, 2, 65, 2, 73, 32, 3, 65, 2, 73, 113, 113, 11] = false := by decide
theorem wrong_section_length_rejected : admitFour [0, 97, 115, 109, 1, 0, 0, 0, 1, 9, 1, 96, 4, 127, 127, 127, 127, 1, 127, 3, 2, 1, 0, 7, 12, 1, 8, 118, 97, 108, 105, 100, 97, 116, 101, 0, 0, 10, 26, 1, 25, 0, 32, 0, 65, 2, 73, 32, 1, 65, 2, 73, 113, 32, 2, 65, 2, 73, 32, 3, 65, 2, 73, 113, 113, 11] = false := by decide
theorem missing_end_rejected : admitFour [0, 97, 115, 109, 1, 0, 0, 0, 1, 9, 1, 96, 4, 127, 127, 127, 127, 1, 127, 3, 2, 1, 0, 7, 12, 1, 8, 118, 97, 108, 105, 100, 97, 116, 101, 0, 0, 10, 27, 1, 25, 0, 32, 0, 65, 2, 73, 32, 1, 65, 2, 73, 113, 32, 2, 65, 2, 73, 32, 3, 65, 2, 73, 113, 113] = false := by decide
theorem trailing_custom_rejected : admitFour [0, 97, 115, 109, 1, 0, 0, 0, 1, 9, 1, 96, 4, 127, 127, 127, 127, 1, 127, 3, 2, 1, 0, 7, 12, 1, 8, 118, 97, 108, 105, 100, 97, 116, 101, 0, 0, 10, 27, 1, 25, 0, 32, 0, 65, 2, 73, 32, 1, 65, 2, 73, 113, 32, 2, 65, 2, 73, 32, 3, 65, 2, 73, 113, 113, 11, 0, 2, 1, 120] = false := by decide
#print axioms actual_admitted
#print axioms actual_correct
#print axioms changed_constant_rejected
#print axioms changed_predicate_rejected
#print axioms changed_opcode_rejected
#print axioms unknown_opcode_rejected
#print axioms wrong_section_length_rejected
#print axioms missing_end_rejected
#print axioms trailing_custom_rejected
