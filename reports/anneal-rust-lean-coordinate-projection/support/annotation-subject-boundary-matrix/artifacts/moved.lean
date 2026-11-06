def helper : Nat := 7
namespace Right
theorem checked : helper = 7 := by rfl
end Right
namespace Selected
theorem checked : helper = 7 := by rfl
end Selected
namespace Test
theorem checked : helper = 7 := by rfl
end Test
namespace Relocated
theorem checked : helper = 7 := by rfl
end Relocated
