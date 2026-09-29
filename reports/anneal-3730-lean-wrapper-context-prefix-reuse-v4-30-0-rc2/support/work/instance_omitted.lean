class Marker where
  value : Nat
instance globalMarker : Marker where
  value := 1
namespace N
theorem proof : (Marker.value : Nat) = 2 := by decide
#print N.proof
#print axioms N.proof
end N
