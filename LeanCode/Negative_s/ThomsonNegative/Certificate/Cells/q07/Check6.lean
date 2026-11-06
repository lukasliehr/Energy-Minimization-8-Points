import ThomsonNegative.Certificate.Cells.q07.Image6
import ThomsonNegative.Certificate.Cells.q07.Stored6

namespace ThomsonNegative.Certificate.Cells.q07
set_option maxRecDepth 8192
set_option maxHeartbeats 100000000
theorem checkpoint6_pass : sameModels image6.coefficients checkpoint6 = true := by decide +kernel
#print axioms checkpoint6_pass
end ThomsonNegative.Certificate.Cells.q07
