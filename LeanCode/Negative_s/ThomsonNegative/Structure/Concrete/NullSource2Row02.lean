import ThomsonNegative.Structure.Concrete.NullKernel
namespace ThomsonNegative.Structure.Concrete.NullKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem source2_row2 : sourceRowCheck 2 2=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.NullKernel
