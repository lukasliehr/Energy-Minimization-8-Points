import ThomsonNegative.Certificate.Correction.q01.Row38

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction38_6 : (centerEquation Source.r38n residual (centers38 6) 3237 65 1071 6).check=true := by decide +kernel
theorem contraction38_7 : (centerEquation Source.r38n residual (centers38 7) 3237 65 1071 7).check=true := by decide +kernel
theorem contraction38_8 : (centerEquation Source.r38n residual (centers38 8) 3237 65 1071 8).check=true := by decide +kernel
theorem contraction38_9 : (centerEquation Source.r38n residual (centers38 9) 3237 65 1071 9).check=true := by decide +kernel
theorem contraction38_10 : (centerEquation Source.r38n residual (centers38 10) 3237 65 1071 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
