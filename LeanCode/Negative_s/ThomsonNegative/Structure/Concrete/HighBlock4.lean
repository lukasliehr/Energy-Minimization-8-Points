import ThomsonNegative.Structure.Concrete.HighKernel
namespace ThomsonNegative.Structure.Concrete.HighKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem block4 : blockCheck 4=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.HighKernel
