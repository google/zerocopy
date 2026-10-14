import WasmValidator
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
open RestrictedWasm
theorem kernel_samples_checked : sampleValidation = true := by decide
#print axioms kernel_samples_checked
