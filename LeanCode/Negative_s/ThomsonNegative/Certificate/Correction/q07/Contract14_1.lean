import ThomsonNegative.Certificate.Correction.q07.Row14

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction14_6 : (centerEquation Source.r14n residual (centers14 6) 3091 24 1024 6).check=true := by decide +kernel
theorem contraction14_7 : (centerEquation Source.r14n residual (centers14 7) 3091 24 1024 7).check=true := by decide +kernel
theorem contraction14_8 : (centerEquation Source.r14n residual (centers14 8) 3091 24 1024 8).check=true := by decide +kernel
theorem contraction14_9 : (centerEquation Source.r14n residual (centers14 9) 3091 24 1024 9).check=true := by decide +kernel
theorem contraction14_10 : (centerEquation Source.r14n residual (centers14 10) 3091 24 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
