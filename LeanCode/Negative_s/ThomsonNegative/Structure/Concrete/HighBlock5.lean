import ThomsonNegative.Structure.Concrete.HighKernel
namespace ThomsonNegative.Structure.Concrete.HighKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem block5 : blockCheck 5=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.HighKernel
