import ThomsonNegative.Certificate.Correction.q09.Row61

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction61_6 : (centerEquation Source.r61n residual (centers61 6) 3085 6 1024 6).check=true := by decide +kernel
theorem contraction61_7 : (centerEquation Source.r61n residual (centers61 7) 3085 6 1024 7).check=true := by decide +kernel
theorem contraction61_8 : (centerEquation Source.r61n residual (centers61 8) 3085 6 1024 8).check=true := by decide +kernel
theorem contraction61_9 : (centerEquation Source.r61n residual (centers61 9) 3085 6 1024 9).check=true := by decide +kernel
theorem contraction61_10 : (centerEquation Source.r61n residual (centers61 10) 3085 6 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
