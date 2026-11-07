import ThomsonNegative.Certificate.Correction.q09.Row58

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction58_0 : (centerEquation Source.r58n residual (centers58 0) 3085 6 1024 0).check=true := by decide +kernel
theorem contraction58_1 : (centerEquation Source.r58n residual (centers58 1) 3085 6 1024 1).check=true := by decide +kernel
theorem contraction58_2 : (centerEquation Source.r58n residual (centers58 2) 3085 6 1024 2).check=true := by decide +kernel
theorem contraction58_3 : (centerEquation Source.r58n residual (centers58 3) 3085 6 1024 3).check=true := by decide +kernel
theorem contraction58_4 : (centerEquation Source.r58n residual (centers58 4) 3085 6 1024 4).check=true := by decide +kernel
theorem contraction58_5 : (centerEquation Source.r58n residual (centers58 5) 3085 6 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
