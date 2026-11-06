import ThomsonNegative.Structure.Concrete.MapKernel
namespace ThomsonNegative.Structure.Concrete.MapKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem col3_chunk8 : chunkCheck 3 8=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.MapKernel
