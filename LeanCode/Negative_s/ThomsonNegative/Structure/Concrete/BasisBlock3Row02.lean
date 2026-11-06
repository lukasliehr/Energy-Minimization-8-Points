import ThomsonNegative.Structure.Concrete.BasisKernel
namespace ThomsonNegative.Structure.Concrete.BasisKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem block3_row2 : rowCheck 3 2 3=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.BasisKernel
