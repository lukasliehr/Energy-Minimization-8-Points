import ThomsonNegative.Certificate.Correction.q09.Row15

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction15_0 : (centerEquation Source.r15n residual (centers15 0) 3092 25 1024 0).check=true := by decide +kernel
theorem contraction15_1 : (centerEquation Source.r15n residual (centers15 1) 3092 25 1024 1).check=true := by decide +kernel
theorem contraction15_2 : (centerEquation Source.r15n residual (centers15 2) 3092 25 1024 2).check=true := by decide +kernel
theorem contraction15_3 : (centerEquation Source.r15n residual (centers15 3) 3092 25 1024 3).check=true := by decide +kernel
theorem contraction15_4 : (centerEquation Source.r15n residual (centers15 4) 3092 25 1024 4).check=true := by decide +kernel
theorem contraction15_5 : (centerEquation Source.r15n residual (centers15 5) 3092 25 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
