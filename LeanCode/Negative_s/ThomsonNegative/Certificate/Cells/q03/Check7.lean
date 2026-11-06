import ThomsonNegative.Certificate.Cells.q03.Image7
import ThomsonNegative.Certificate.Cells.q03.Stored7

namespace ThomsonNegative.Certificate.Cells.q03
set_option maxRecDepth 8192
set_option maxHeartbeats 100000000
theorem checkpoint7_pass : sameModels image7.coefficients checkpoint7 = true := by decide +kernel
#print axioms checkpoint7_pass
end ThomsonNegative.Certificate.Cells.q03
