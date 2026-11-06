import ThomsonNegative.Certificate.Cells.q05.Image3
import ThomsonNegative.Certificate.Cells.q05.Stored3

namespace ThomsonNegative.Certificate.Cells.q05
set_option maxRecDepth 8192
set_option maxHeartbeats 100000000
theorem checkpoint3_pass : sameModels image3.coefficients checkpoint3 = true := by decide +kernel
#print axioms checkpoint3_pass
end ThomsonNegative.Certificate.Cells.q05
