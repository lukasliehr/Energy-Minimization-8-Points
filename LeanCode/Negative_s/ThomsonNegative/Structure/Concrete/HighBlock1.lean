import ThomsonNegative.Structure.Concrete.HighKernel
namespace ThomsonNegative.Structure.Concrete.HighKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem block1 : blockCheck 1=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.HighKernel
