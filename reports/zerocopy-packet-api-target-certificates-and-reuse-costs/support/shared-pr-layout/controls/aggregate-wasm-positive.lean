import LayoutBridge
open LayoutBridge
theorem consumed_aggregate : AggregateGeometry .wasm32 [12,4,4,8,1,1,4,1,2,1,4,4] :=
  admitted_aggregate_geometry .wasm32 [12,4,4,8,1,1,4,1,2,1,4,4] (by decide)
#print axioms consumed_aggregate
