import ThomsonNegative.Certificate.Correction.q01.Row30

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction30_6 : (centerEquation Source.r30n residual (centers30 6) 3255 65 1077 6).check=true := by decide +kernel
theorem contraction30_7 : (centerEquation Source.r30n residual (centers30 7) 3255 65 1077 7).check=true := by decide +kernel
theorem contraction30_8 : (centerEquation Source.r30n residual (centers30 8) 3255 65 1077 8).check=true := by decide +kernel
theorem contraction30_9 : (centerEquation Source.r30n residual (centers30 9) 3255 65 1077 9).check=true := by decide +kernel
theorem contraction30_10 : (centerEquation Source.r30n residual (centers30 10) 3255 65 1077 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
