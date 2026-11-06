import ThomsonNegative.Structure.Concrete.MapKernel
namespace ThomsonNegative.Structure.Concrete.MapKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem col8_chunk3 : chunkCheck 8 3=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.MapKernel
