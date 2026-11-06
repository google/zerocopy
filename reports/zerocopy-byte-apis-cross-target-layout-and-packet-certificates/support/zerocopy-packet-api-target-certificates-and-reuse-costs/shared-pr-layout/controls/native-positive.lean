import LayoutBridge
open LayoutBridge
theorem consumed_observation : ObservedGeometry .native64 [8,4,1,2,1] :=
  admitted_geometry .native64 [8,4,1,2,1] (by decide)
#print axioms consumed_observation
