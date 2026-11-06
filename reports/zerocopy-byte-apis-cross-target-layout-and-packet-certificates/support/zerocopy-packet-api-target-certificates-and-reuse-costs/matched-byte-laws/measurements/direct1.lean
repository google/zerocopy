import ByteLaws
open ByteLaws
theorem universal_into (s : Memory) : IntoLaw s := into_direct s
#print axioms universal_into
theorem universal_write (s : Memory) (a f : Addr) (v : Byte) : WriteLaw s a f v := write_direct s a f v
#print axioms universal_write
theorem universal_boolean (s t : Memory) (a : Addr) : BoolLaw s t a := bool_direct s t a
#print axioms universal_boolean
theorem universal_array (s t : Memory) : ArrayLaw s t := array_direct s t
#print axioms universal_array
theorem concrete_into : IntoLaw base := into_direct base
#print axioms concrete_into
theorem concrete_write : WriteLaw base false true 2 := write_direct base false true 2
#print axioms concrete_write
theorem concrete_boolean : BoolLaw base base false := bool_direct base base false
#print axioms concrete_boolean
theorem concrete_array : ArrayLaw base base := array_direct base base
#print axioms concrete_array
