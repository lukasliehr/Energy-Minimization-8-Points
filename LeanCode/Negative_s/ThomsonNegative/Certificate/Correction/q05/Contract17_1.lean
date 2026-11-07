import ThomsonNegative.Certificate.Correction.q05.Row17

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction17_6 : (centerEquation Source.r17n residual (centers17 6) 3078 1 1024 6).check=true := by decide +kernel
theorem contraction17_7 : (centerEquation Source.r17n residual (centers17 7) 3078 1 1024 7).check=true := by decide +kernel
theorem contraction17_8 : (centerEquation Source.r17n residual (centers17 8) 3078 1 1024 8).check=true := by decide +kernel
theorem contraction17_9 : (centerEquation Source.r17n residual (centers17 9) 3078 1 1024 9).check=true := by decide +kernel
theorem contraction17_10 : (centerEquation Source.r17n residual (centers17 10) 3078 1 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
