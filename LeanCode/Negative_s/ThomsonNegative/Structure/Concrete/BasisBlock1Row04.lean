import ThomsonNegative.Structure.Concrete.BasisKernel
namespace ThomsonNegative.Structure.Concrete.BasisKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem block1_row4 : rowCheck 1 4 5=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.BasisKernel
