import ThomsonNegative.Structure.Factored.complement_inverse.Config
namespace ThomsonNegative.Structure.Factored.complement_inverse
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem column_1 : columnCheck 1 = true := by decide +kernel
end ThomsonNegative.Structure.Factored.complement_inverse
