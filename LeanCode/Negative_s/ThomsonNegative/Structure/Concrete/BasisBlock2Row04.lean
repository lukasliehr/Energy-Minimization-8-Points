import ThomsonNegative.Structure.Concrete.BasisKernel
namespace ThomsonNegative.Structure.Concrete.BasisKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem block2_row4 : rowCheck 2 4 4=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.BasisKernel
