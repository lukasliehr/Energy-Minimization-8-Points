import ThomsonNegative.Certificate.Correction.q03.Row30

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction30_0 : (centerEquation Source.r30n residual (centers30 0) 3255 65 1077 0).check=true := by decide +kernel
theorem contraction30_1 : (centerEquation Source.r30n residual (centers30 1) 3255 65 1077 1).check=true := by decide +kernel
theorem contraction30_2 : (centerEquation Source.r30n residual (centers30 2) 3255 65 1077 2).check=true := by decide +kernel
theorem contraction30_3 : (centerEquation Source.r30n residual (centers30 3) 3255 65 1077 3).check=true := by decide +kernel
theorem contraction30_4 : (centerEquation Source.r30n residual (centers30 4) 3255 65 1077 4).check=true := by decide +kernel
theorem contraction30_5 : (centerEquation Source.r30n residual (centers30 5) 3255 65 1077 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
