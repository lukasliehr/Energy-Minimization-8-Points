import ThomsonNegative.Certificate.Correction.q03.Row17

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction17_0 : (centerEquation Source.r17n residual (centers17 0) 3078 1 1024 0).check=true := by decide +kernel
theorem contraction17_1 : (centerEquation Source.r17n residual (centers17 1) 3078 1 1024 1).check=true := by decide +kernel
theorem contraction17_2 : (centerEquation Source.r17n residual (centers17 2) 3078 1 1024 2).check=true := by decide +kernel
theorem contraction17_3 : (centerEquation Source.r17n residual (centers17 3) 3078 1 1024 3).check=true := by decide +kernel
theorem contraction17_4 : (centerEquation Source.r17n residual (centers17 4) 3078 1 1024 4).check=true := by decide +kernel
theorem contraction17_5 : (centerEquation Source.r17n residual (centers17 5) 3078 1 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
