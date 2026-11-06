import ThomsonNegative.Certificate.Correction.q01.Row24

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction24_0 : (centerEquation Source.r24n residual (centers24 0) 3095 55 1024 0).check=true := by decide +kernel
theorem contraction24_1 : (centerEquation Source.r24n residual (centers24 1) 3095 55 1024 1).check=true := by decide +kernel
theorem contraction24_2 : (centerEquation Source.r24n residual (centers24 2) 3095 55 1024 2).check=true := by decide +kernel
theorem contraction24_3 : (centerEquation Source.r24n residual (centers24 3) 3095 55 1024 3).check=true := by decide +kernel
theorem contraction24_4 : (centerEquation Source.r24n residual (centers24 4) 3095 55 1024 4).check=true := by decide +kernel
theorem contraction24_5 : (centerEquation Source.r24n residual (centers24 5) 3095 55 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
