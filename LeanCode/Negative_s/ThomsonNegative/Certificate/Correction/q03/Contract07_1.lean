import ThomsonNegative.Certificate.Correction.q03.Row07

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction7_6 : (centerEquation Source.r7n residual (centers7 6) 3094 44 1024 6).check=true := by decide +kernel
theorem contraction7_7 : (centerEquation Source.r7n residual (centers7 7) 3094 44 1024 7).check=true := by decide +kernel
theorem contraction7_8 : (centerEquation Source.r7n residual (centers7 8) 3094 44 1024 8).check=true := by decide +kernel
theorem contraction7_9 : (centerEquation Source.r7n residual (centers7 9) 3094 44 1024 9).check=true := by decide +kernel
theorem contraction7_10 : (centerEquation Source.r7n residual (centers7 10) 3094 44 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
