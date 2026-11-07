import ThomsonNegative.Structure.Concrete.MapKernel
namespace ThomsonNegative.Structure.Concrete.MapKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem col6_chunk3 : chunkCheck 6 3=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.MapKernel
