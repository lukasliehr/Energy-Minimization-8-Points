import ThomsonNegative.Certificate.Correction.q05.Row38

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction38_0 : (centerEquation Source.r38n residual (centers38 0) 3246 65 1074 0).check=true := by decide +kernel
theorem contraction38_1 : (centerEquation Source.r38n residual (centers38 1) 3246 65 1074 1).check=true := by decide +kernel
theorem contraction38_2 : (centerEquation Source.r38n residual (centers38 2) 3246 65 1074 2).check=true := by decide +kernel
theorem contraction38_3 : (centerEquation Source.r38n residual (centers38 3) 3246 65 1074 3).check=true := by decide +kernel
theorem contraction38_4 : (centerEquation Source.r38n residual (centers38 4) 3246 65 1074 4).check=true := by decide +kernel
theorem contraction38_5 : (centerEquation Source.r38n residual (centers38 5) 3246 65 1074 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
