import ThomsonNegative.Certificate.Correction.q09.Row61

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction61_0 : (centerEquation Source.r61n residual (centers61 0) 3085 6 1024 0).check=true := by decide +kernel
theorem contraction61_1 : (centerEquation Source.r61n residual (centers61 1) 3085 6 1024 1).check=true := by decide +kernel
theorem contraction61_2 : (centerEquation Source.r61n residual (centers61 2) 3085 6 1024 2).check=true := by decide +kernel
theorem contraction61_3 : (centerEquation Source.r61n residual (centers61 3) 3085 6 1024 3).check=true := by decide +kernel
theorem contraction61_4 : (centerEquation Source.r61n residual (centers61 4) 3085 6 1024 4).check=true := by decide +kernel
theorem contraction61_5 : (centerEquation Source.r61n residual (centers61 5) 3085 6 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
