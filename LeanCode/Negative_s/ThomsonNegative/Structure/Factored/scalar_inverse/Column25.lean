import ThomsonNegative.Structure.Factored.scalar_inverse.Config
namespace ThomsonNegative.Structure.Factored.scalar_inverse
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem column_25 : columnCheck 25 = true := by decide +kernel
end ThomsonNegative.Structure.Factored.scalar_inverse
