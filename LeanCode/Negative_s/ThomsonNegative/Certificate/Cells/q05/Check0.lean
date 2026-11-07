import ThomsonNegative.Certificate.Cells.q05.Image0
import ThomsonNegative.Certificate.Cells.q05.Stored0

namespace ThomsonNegative.Certificate.Cells.q05
set_option maxRecDepth 8192
set_option maxHeartbeats 100000000
theorem checkpoint0_pass : sameModels image0.coefficients checkpoint0 = true := by decide +kernel
#print axioms checkpoint0_pass
end ThomsonNegative.Certificate.Cells.q05
