import ThomsonNegative.Structure.Concrete.NullKernel
namespace ThomsonNegative.Structure.Concrete.NullKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem null2_col2 : nullColumnCheck 2 2=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.NullKernel
