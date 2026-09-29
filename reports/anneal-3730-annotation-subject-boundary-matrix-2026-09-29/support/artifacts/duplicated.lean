def helper : Nat := 7
namespace Left
theorem checked : helper = 7 := by rfl
end Left
namespace Copied
theorem checked : helper = 7 := by rfl
end Copied
namespace Right
theorem checked : helper = 7 := by rfl
end Right
namespace Selected
theorem checked : helper = 7 := by rfl
end Selected
namespace Test
theorem checked : helper = 7 := by rfl
end Test
