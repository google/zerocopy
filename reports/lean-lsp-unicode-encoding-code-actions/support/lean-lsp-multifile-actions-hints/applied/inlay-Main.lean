import Helper
#check αhelper
def use_helper : Nat := αhelper 2
def add_three (x : Nat) (y : Nat) : Nat := x + y + 3
#check add_three 1 2
def infer := αhelper 3
theorem auto_hint {α} (x : α) : x = x := rfl
def call_demo : Nat := add_three 1 2
