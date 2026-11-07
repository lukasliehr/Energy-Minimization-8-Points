import ThomsonNegative.Certificate.Correction.q09.Row38

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction38_6 : (centerEquation Source.r38n residual (centers38 6) 3249 65 1075 6).check=true := by decide +kernel
theorem contraction38_7 : (centerEquation Source.r38n residual (centers38 7) 3249 65 1075 7).check=true := by decide +kernel
theorem contraction38_8 : (centerEquation Source.r38n residual (centers38 8) 3249 65 1075 8).check=true := by decide +kernel
theorem contraction38_9 : (centerEquation Source.r38n residual (centers38 9) 3249 65 1075 9).check=true := by decide +kernel
theorem contraction38_10 : (centerEquation Source.r38n residual (centers38 10) 3249 65 1075 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
