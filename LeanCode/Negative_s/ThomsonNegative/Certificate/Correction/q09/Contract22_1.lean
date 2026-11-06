import ThomsonNegative.Certificate.Correction.q09.Row22

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction22_6 : (centerEquation Source.r22n residual (centers22 6) 3219 64 1065 6).check=true := by decide +kernel
theorem contraction22_7 : (centerEquation Source.r22n residual (centers22 7) 3219 64 1065 7).check=true := by decide +kernel
theorem contraction22_8 : (centerEquation Source.r22n residual (centers22 8) 3219 64 1065 8).check=true := by decide +kernel
theorem contraction22_9 : (centerEquation Source.r22n residual (centers22 9) 3219 64 1065 9).check=true := by decide +kernel
theorem contraction22_10 : (centerEquation Source.r22n residual (centers22 10) 3219 64 1065 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
