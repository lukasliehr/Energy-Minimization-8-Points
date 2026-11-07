import ThomsonNegative.Certificate.Correction.q07.Row07

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction7_0 : (centerEquation Source.r7n residual (centers7 0) 3094 44 1024 0).check=true := by decide +kernel
theorem contraction7_1 : (centerEquation Source.r7n residual (centers7 1) 3094 44 1024 1).check=true := by decide +kernel
theorem contraction7_2 : (centerEquation Source.r7n residual (centers7 2) 3094 44 1024 2).check=true := by decide +kernel
theorem contraction7_3 : (centerEquation Source.r7n residual (centers7 3) 3094 44 1024 3).check=true := by decide +kernel
theorem contraction7_4 : (centerEquation Source.r7n residual (centers7 4) 3094 44 1024 4).check=true := by decide +kernel
theorem contraction7_5 : (centerEquation Source.r7n residual (centers7 5) 3094 44 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
