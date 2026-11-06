import Dep
theorem demo (n : Nat) (h : n = 1) : n + sharedValue = 1 + sharedValue := by
  exact congrArg (fun x => x + sharedValue) h
