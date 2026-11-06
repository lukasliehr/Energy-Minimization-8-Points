import ThomsonNegative.Certificate.Correction.q03.Row31

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction31_6 : (centerEquation Source.r31n residual (centers31 6) 3095 56 1024 6).check=true := by decide +kernel
theorem contraction31_7 : (centerEquation Source.r31n residual (centers31 7) 3095 56 1024 7).check=true := by decide +kernel
theorem contraction31_8 : (centerEquation Source.r31n residual (centers31 8) 3095 56 1024 8).check=true := by decide +kernel
theorem contraction31_9 : (centerEquation Source.r31n residual (centers31 9) 3095 56 1024 9).check=true := by decide +kernel
theorem contraction31_10 : (centerEquation Source.r31n residual (centers31 10) 3095 56 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
