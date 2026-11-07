import ThomsonNegative.Certificate.Cells.q01.Image2
import ThomsonNegative.Certificate.Cells.q01.Stored2

namespace ThomsonNegative.Certificate.Cells.q01
set_option maxRecDepth 8192
set_option maxHeartbeats 100000000
theorem checkpoint2_pass : sameModels image2.coefficients checkpoint2 = true := by decide +kernel
#print axioms checkpoint2_pass
end ThomsonNegative.Certificate.Cells.q01
