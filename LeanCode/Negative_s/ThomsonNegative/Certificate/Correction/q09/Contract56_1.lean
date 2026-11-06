import ThomsonNegative.Certificate.Correction.q09.Row56

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction56_6 : (centerEquation Source.r56n residual (centers56 6) 3085 6 1024 6).check=true := by decide +kernel
theorem contraction56_7 : (centerEquation Source.r56n residual (centers56 7) 3085 6 1024 7).check=true := by decide +kernel
theorem contraction56_8 : (centerEquation Source.r56n residual (centers56 8) 3085 6 1024 8).check=true := by decide +kernel
theorem contraction56_9 : (centerEquation Source.r56n residual (centers56 9) 3085 6 1024 9).check=true := by decide +kernel
theorem contraction56_10 : (centerEquation Source.r56n residual (centers56 10) 3085 6 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
