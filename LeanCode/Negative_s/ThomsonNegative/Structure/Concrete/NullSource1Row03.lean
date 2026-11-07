import ThomsonNegative.Structure.Concrete.NullKernel
namespace ThomsonNegative.Structure.Concrete.NullKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem source1_row3 : sourceRowCheck 1 3=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.NullKernel
