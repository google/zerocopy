import Helper
#check βhelper
def use_helper : Nat := βhelper 2
def add_three (x : Nat) (y : Nat) : Nat := x + y + 3
#check add_three 1 2
def infer := βhelper 3
theorem auto_hint (x : α) : x = x := rfl
def call_demo : Nat := add_three 1 2
