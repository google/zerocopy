import LayoutBridge
open LayoutBridge
theorem consumed_aggregate : AggregateGeometry .native64 [16,8,8,12,1,1,4,1,2,1,8,8] :=
  admitted_aggregate_geometry .native64 [16,8,8,12,1,1,4,1,2,1,8,8] (by decide)
#print axioms consumed_aggregate
