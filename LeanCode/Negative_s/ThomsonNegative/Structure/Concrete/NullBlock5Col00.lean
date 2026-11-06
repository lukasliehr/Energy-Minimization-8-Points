import ThomsonNegative.Structure.Concrete.NullKernel
namespace ThomsonNegative.Structure.Concrete.NullKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem null5_col0 : nullColumnCheck 5 0=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.NullKernel
