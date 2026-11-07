import ThomsonNegative.Certificate.Correction.q01.Row18

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction18_0 : (centerEquation Source.r18n residual (centers18 0) 3113 62 1030 0).check=true := by decide +kernel
theorem contraction18_1 : (centerEquation Source.r18n residual (centers18 1) 3113 62 1030 1).check=true := by decide +kernel
theorem contraction18_2 : (centerEquation Source.r18n residual (centers18 2) 3113 62 1030 2).check=true := by decide +kernel
theorem contraction18_3 : (centerEquation Source.r18n residual (centers18 3) 3113 62 1030 3).check=true := by decide +kernel
theorem contraction18_4 : (centerEquation Source.r18n residual (centers18 4) 3113 62 1030 4).check=true := by decide +kernel
theorem contraction18_5 : (centerEquation Source.r18n residual (centers18 5) 3113 62 1030 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
