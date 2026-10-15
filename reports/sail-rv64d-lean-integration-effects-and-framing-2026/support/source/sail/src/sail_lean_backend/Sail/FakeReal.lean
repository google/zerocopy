import Sail
import THE_MODULE_NAME.Defs

namespace THE_MODULE_NAME

abbrev real := Float

-- val "neg_real" : real -> real
def neg_real (x : real) : real := -x

-- val "mult_real" : (real, real) -> real
def mult_real (x y : real) : real := x * y

-- val "sub_real" : (real, real) -> real
def sub_real (x y : real) : real := x - y

-- val "add_real" : (real, real) -> real
def add_real (x y : real) : real := x + y

-- val "div_real" : (real, real) -> real
def div_real (x y : real) : real := x / y

-- val sqrt = pure "sqrt_real" : real -> real
def sqrt_real (x : real) : real := Float.sqrt x

-- val "abs_real" : real -> real
def abs_real (x : real) : real := x.abs

-- val floor = pure "round_down" : real -> int
def round_down (x : real) : Int := x.toUInt64.toNat

-- val ceil = pure "round_up" : real -> int
def round_up (x : real) : Int := round_down (x + 0.5)

-- val "to_real" : int -> real
def to_real (x : Int) : real := Float.ofInt x

-- val "eq_real" : (real, real) -> bool
def eq_real (x y : real) : Bool := x == y

-- val "lt_real" : (real, real) -> bool
def lt_real (x y : real) : Bool := x < y

-- val "gt_real" : (real, real) -> bool
def gt_real (x y : real) : Bool := x > y

-- val "lteq_real" : (real, real) -> bool
def lteq_real (x y : real) : Bool := x ≤ y

-- val "gteq_real" : (real, real) -> bool
def gteq_real (x y : real) : Bool := x ≥ y

-- val pow_real = pure "real_power" : (real, int) -> real
def real_power (x : real) (n : Int) : real := Float.pow x (Float.ofInt n)

-- val "print_real" : (string, real) -> unit
def print_real (_ : String) (_ : real) : Unit := ()

-- val "prerr_real" : (string, real) -> unit
def prerr_real (_ : String) (_ : real) : Unit := ()

-- val "random_real" : unit -> real
def random_real (_ : Unit) : real := 34

def undefined_real (_ : Unit) : SailM real := return default
