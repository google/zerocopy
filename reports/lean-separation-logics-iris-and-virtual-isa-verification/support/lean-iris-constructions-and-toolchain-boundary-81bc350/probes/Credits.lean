module
public import Init
namespace GapProbe
@[expose] public section
abbrev Credit := Nat
 def join (a b : Credit) : Credit := a + b
 theorem join_comm (a b : Credit) : join a b = join b a := Nat.add_comm a b
#print axioms join_comm
end
end GapProbe
