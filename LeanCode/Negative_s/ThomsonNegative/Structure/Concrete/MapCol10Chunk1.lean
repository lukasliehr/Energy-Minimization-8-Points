import ThomsonNegative.Structure.Concrete.MapKernel
namespace ThomsonNegative.Structure.Concrete.MapKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem col10_chunk1 : chunkCheck 10 1=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.MapKernel
