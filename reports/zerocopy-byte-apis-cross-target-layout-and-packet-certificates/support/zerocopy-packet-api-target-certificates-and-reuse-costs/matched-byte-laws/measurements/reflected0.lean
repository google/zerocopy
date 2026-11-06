import ByteLaws
open ByteLaws
theorem universal_into (s : Memory) : IntoLaw s := check_sound (.into s) (all_reflected (.into s))
#print axioms universal_into
theorem universal_write (s : Memory) (a f : Addr) (v : Byte) : WriteLaw s a f v := check_sound (.write s a f v) (all_reflected (.write s a f v))
#print axioms universal_write
theorem universal_boolean (s t : Memory) (a : Addr) : BoolLaw s t a := check_sound (.boolean s t a) (all_reflected (.boolean s t a))
#print axioms universal_boolean
theorem universal_array (s t : Memory) : ArrayLaw s t := check_sound (.array s t) (all_reflected (.array s t))
#print axioms universal_array
theorem concrete_into : IntoLaw base := check_sound (.into base) (by decide)
#print axioms concrete_into
theorem concrete_write : WriteLaw base false true 2 := check_sound (.write base false true 2) (by decide)
#print axioms concrete_write
theorem concrete_boolean : BoolLaw base base false := check_sound (.boolean base base false) (by decide)
#print axioms concrete_boolean
theorem concrete_array : ArrayLaw base base := check_sound (.array base base) (by decide)
#print axioms concrete_array
