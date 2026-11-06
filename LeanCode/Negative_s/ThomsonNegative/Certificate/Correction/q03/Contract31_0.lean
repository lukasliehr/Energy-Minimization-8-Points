import ThomsonNegative.Certificate.Correction.q03.Row31

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction31_0 : (centerEquation Source.r31n residual (centers31 0) 3095 56 1024 0).check=true := by decide +kernel
theorem contraction31_1 : (centerEquation Source.r31n residual (centers31 1) 3095 56 1024 1).check=true := by decide +kernel
theorem contraction31_2 : (centerEquation Source.r31n residual (centers31 2) 3095 56 1024 2).check=true := by decide +kernel
theorem contraction31_3 : (centerEquation Source.r31n residual (centers31 3) 3095 56 1024 3).check=true := by decide +kernel
theorem contraction31_4 : (centerEquation Source.r31n residual (centers31 4) 3095 56 1024 4).check=true := by decide +kernel
theorem contraction31_5 : (centerEquation Source.r31n residual (centers31 5) 3095 56 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
