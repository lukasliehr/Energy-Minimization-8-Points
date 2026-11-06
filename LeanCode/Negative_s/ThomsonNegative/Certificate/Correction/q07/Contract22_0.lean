import ThomsonNegative.Certificate.Correction.q07.Row22

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction22_0 : (centerEquation Source.r22n residual (centers22 0) 3216 64 1064 0).check=true := by decide +kernel
theorem contraction22_1 : (centerEquation Source.r22n residual (centers22 1) 3216 64 1064 1).check=true := by decide +kernel
theorem contraction22_2 : (centerEquation Source.r22n residual (centers22 2) 3216 64 1064 2).check=true := by decide +kernel
theorem contraction22_3 : (centerEquation Source.r22n residual (centers22 3) 3216 64 1064 3).check=true := by decide +kernel
theorem contraction22_4 : (centerEquation Source.r22n residual (centers22 4) 3216 64 1064 4).check=true := by decide +kernel
theorem contraction22_5 : (centerEquation Source.r22n residual (centers22 5) 3216 64 1064 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
