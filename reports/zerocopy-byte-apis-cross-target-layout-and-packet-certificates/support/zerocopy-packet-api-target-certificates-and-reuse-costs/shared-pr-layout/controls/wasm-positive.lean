import LayoutBridge
open LayoutBridge
theorem consumed_observation : ObservedGeometry .wasm32 [4,4,1,2,1] :=
  admitted_geometry .wasm32 [4,4,1,2,1] (by decide)
#print axioms consumed_observation
