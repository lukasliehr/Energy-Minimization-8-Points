import ThomsonNegative.Certificate.Cells.q05.Image5
import ThomsonNegative.Certificate.Cells.q05.Stored5

namespace ThomsonNegative.Certificate.Cells.q05
set_option maxRecDepth 8192
set_option maxHeartbeats 100000000
theorem checkpoint5_pass : sameModels image5.coefficients checkpoint5 = true := by decide +kernel
#print axioms checkpoint5_pass
end ThomsonNegative.Certificate.Cells.q05
