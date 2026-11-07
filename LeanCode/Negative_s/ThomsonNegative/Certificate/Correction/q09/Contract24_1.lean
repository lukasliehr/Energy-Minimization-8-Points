import ThomsonNegative.Certificate.Correction.q09.Row24

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction24_6 : (centerEquation Source.r24n residual (centers24 6) 3095 55 1024 6).check=true := by decide +kernel
theorem contraction24_7 : (centerEquation Source.r24n residual (centers24 7) 3095 55 1024 7).check=true := by decide +kernel
theorem contraction24_8 : (centerEquation Source.r24n residual (centers24 8) 3095 55 1024 8).check=true := by decide +kernel
theorem contraction24_9 : (centerEquation Source.r24n residual (centers24 9) 3095 55 1024 9).check=true := by decide +kernel
theorem contraction24_10 : (centerEquation Source.r24n residual (centers24 10) 3095 55 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
