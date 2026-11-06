import ThomsonNegative.Structure.Concrete.MapKernel
namespace ThomsonNegative.Structure.Concrete.MapKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem col42_chunk4 : chunkCheck 42 4=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.MapKernel
