import ThomsonNegative.Certificate.Cells.q03.Image1
import ThomsonNegative.Certificate.Cells.q03.Stored1

namespace ThomsonNegative.Certificate.Cells.q03
set_option maxRecDepth 8192
set_option maxHeartbeats 100000000
theorem checkpoint1_pass : sameModels image1.coefficients checkpoint1 = true := by decide +kernel
#print axioms checkpoint1_pass
end ThomsonNegative.Certificate.Cells.q03
