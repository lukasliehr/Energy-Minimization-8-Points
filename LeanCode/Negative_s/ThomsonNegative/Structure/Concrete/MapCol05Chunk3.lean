import ThomsonNegative.Structure.Concrete.MapKernel
namespace ThomsonNegative.Structure.Concrete.MapKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem col5_chunk3 : chunkCheck 5 3=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.MapKernel
