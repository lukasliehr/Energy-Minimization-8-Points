import ThomsonNegative.Structure.Concrete.MapKernel
namespace ThomsonNegative.Structure.Concrete.MapKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem col12_chunk4 : chunkCheck 12 4=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.MapKernel
