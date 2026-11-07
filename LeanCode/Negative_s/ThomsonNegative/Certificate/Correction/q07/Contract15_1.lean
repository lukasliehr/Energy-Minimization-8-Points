import ThomsonNegative.Certificate.Correction.q07.Row15

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction15_6 : (centerEquation Source.r15n residual (centers15 6) 3092 25 1024 6).check=true := by decide +kernel
theorem contraction15_7 : (centerEquation Source.r15n residual (centers15 7) 3092 25 1024 7).check=true := by decide +kernel
theorem contraction15_8 : (centerEquation Source.r15n residual (centers15 8) 3092 25 1024 8).check=true := by decide +kernel
theorem contraction15_9 : (centerEquation Source.r15n residual (centers15 9) 3092 25 1024 9).check=true := by decide +kernel
theorem contraction15_10 : (centerEquation Source.r15n residual (centers15 10) 3092 25 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
