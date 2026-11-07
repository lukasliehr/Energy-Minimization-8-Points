import ThomsonNegative.Structure.Concrete.SymmetryKernel
namespace ThomsonNegative.Structure.Concrete.SymmetryKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem block3 : blockCheck 3=true := by decide +kernel
end ThomsonNegative.Structure.Concrete.SymmetryKernel
