import ThomsonNegative.Certificate.Correction.q03.Row35

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction35_0 : (centerEquation Source.r35n residual (centers35 0) 3095 55 1024 0).check=true := by decide +kernel
theorem contraction35_1 : (centerEquation Source.r35n residual (centers35 1) 3095 55 1024 1).check=true := by decide +kernel
theorem contraction35_2 : (centerEquation Source.r35n residual (centers35 2) 3095 55 1024 2).check=true := by decide +kernel
theorem contraction35_3 : (centerEquation Source.r35n residual (centers35 3) 3095 55 1024 3).check=true := by decide +kernel
theorem contraction35_4 : (centerEquation Source.r35n residual (centers35 4) 3095 55 1024 4).check=true := by decide +kernel
theorem contraction35_5 : (centerEquation Source.r35n residual (centers35 5) 3095 55 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
