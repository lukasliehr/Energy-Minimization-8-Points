import ThomsonNegative.Certificate.Cells.q07.Image4
import ThomsonNegative.Certificate.Cells.q07.Stored4

namespace ThomsonNegative.Certificate.Cells.q07
set_option maxRecDepth 8192
set_option maxHeartbeats 100000000
theorem checkpoint4_pass : sameModels image4.coefficients checkpoint4 = true := by decide +kernel
#print axioms checkpoint4_pass
end ThomsonNegative.Certificate.Cells.q07
