import ThomsonNegative.Certificate.Correction.q07.Row14

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction14_0 : (centerEquation Source.r14n residual (centers14 0) 3091 24 1024 0).check=true := by decide +kernel
theorem contraction14_1 : (centerEquation Source.r14n residual (centers14 1) 3091 24 1024 1).check=true := by decide +kernel
theorem contraction14_2 : (centerEquation Source.r14n residual (centers14 2) 3091 24 1024 2).check=true := by decide +kernel
theorem contraction14_3 : (centerEquation Source.r14n residual (centers14 3) 3091 24 1024 3).check=true := by decide +kernel
theorem contraction14_4 : (centerEquation Source.r14n residual (centers14 4) 3091 24 1024 4).check=true := by decide +kernel
theorem contraction14_5 : (centerEquation Source.r14n residual (centers14 5) 3091 24 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
