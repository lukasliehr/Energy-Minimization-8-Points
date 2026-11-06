import ThomsonNegative.Certificate.Correction.q09.Row26

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction26_6 : (centerEquation Source.r26n residual (centers26 6) 3095 59 1024 6).check=true := by decide +kernel
theorem contraction26_7 : (centerEquation Source.r26n residual (centers26 7) 3095 59 1024 7).check=true := by decide +kernel
theorem contraction26_8 : (centerEquation Source.r26n residual (centers26 8) 3095 59 1024 8).check=true := by decide +kernel
theorem contraction26_9 : (centerEquation Source.r26n residual (centers26 9) 3095 59 1024 9).check=true := by decide +kernel
theorem contraction26_10 : (centerEquation Source.r26n residual (centers26 10) 3095 59 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
