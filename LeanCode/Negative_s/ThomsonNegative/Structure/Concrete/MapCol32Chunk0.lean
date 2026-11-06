import ThomsonNegative.Structure.Concrete.MapKernel
namespace ThomsonNegative.Structure.Concrete.MapKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem col32_chunk0 : chunkCheck 32 0=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.MapKernel
