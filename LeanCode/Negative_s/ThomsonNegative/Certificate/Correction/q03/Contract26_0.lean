import ThomsonNegative.Certificate.Correction.q03.Row26

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction26_0 : (centerEquation Source.r26n residual (centers26 0) 3095 59 1024 0).check=true := by decide +kernel
theorem contraction26_1 : (centerEquation Source.r26n residual (centers26 1) 3095 59 1024 1).check=true := by decide +kernel
theorem contraction26_2 : (centerEquation Source.r26n residual (centers26 2) 3095 59 1024 2).check=true := by decide +kernel
theorem contraction26_3 : (centerEquation Source.r26n residual (centers26 3) 3095 59 1024 3).check=true := by decide +kernel
theorem contraction26_4 : (centerEquation Source.r26n residual (centers26 4) 3095 59 1024 4).check=true := by decide +kernel
theorem contraction26_5 : (centerEquation Source.r26n residual (centers26 5) 3095 59 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
