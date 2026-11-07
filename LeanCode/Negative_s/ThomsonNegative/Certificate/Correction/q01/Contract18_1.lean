import ThomsonNegative.Certificate.Correction.q01.Row18

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction18_6 : (centerEquation Source.r18n residual (centers18 6) 3113 62 1030 6).check=true := by decide +kernel
theorem contraction18_7 : (centerEquation Source.r18n residual (centers18 7) 3113 62 1030 7).check=true := by decide +kernel
theorem contraction18_8 : (centerEquation Source.r18n residual (centers18 8) 3113 62 1030 8).check=true := by decide +kernel
theorem contraction18_9 : (centerEquation Source.r18n residual (centers18 9) 3113 62 1030 9).check=true := by decide +kernel
theorem contraction18_10 : (centerEquation Source.r18n residual (centers18 10) 3113 62 1030 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
