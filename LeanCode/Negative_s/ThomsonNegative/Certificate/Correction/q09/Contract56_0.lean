import ThomsonNegative.Certificate.Correction.q09.Row56

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction56_0 : (centerEquation Source.r56n residual (centers56 0) 3085 6 1024 0).check=true := by decide +kernel
theorem contraction56_1 : (centerEquation Source.r56n residual (centers56 1) 3085 6 1024 1).check=true := by decide +kernel
theorem contraction56_2 : (centerEquation Source.r56n residual (centers56 2) 3085 6 1024 2).check=true := by decide +kernel
theorem contraction56_3 : (centerEquation Source.r56n residual (centers56 3) 3085 6 1024 3).check=true := by decide +kernel
theorem contraction56_4 : (centerEquation Source.r56n residual (centers56 4) 3085 6 1024 4).check=true := by decide +kernel
theorem contraction56_5 : (centerEquation Source.r56n residual (centers56 5) 3085 6 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
